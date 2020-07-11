// formal model for discretionary access control (DAC)
// can be verified and visualized using Alloy Tools GUI
// developed by Serge (vinahradau@yahoo.de)

module DiscretionaryAccessControl

enum PERMISSION {READ, WRITE, EXECUTE}

enum DIRECTORY_ID {DIRECTORY_1, DIRECTORY_2, DIRECTORY_3, DIRECTORY_4, DIRECTORY_5}

enum FILE_ID {FILE_1, FILE_2, FILE_3, FILE_4, FILE_5}

enum USER_ID {USER_1, USER_2, USER_3, USER_4, USER_5}

enum GROUP_ID {GROUP_1, GROUP_2, GROUP_3, GROUP_4, GROUP_5}

enum CONTENT {CONTENT_1, CONTENT_2, CONTENT_3, CONTENT_4, CONTENT_5}

abstract sig RESOURCE{
permissions: PERMISSIONS
}{
}

sig SYSTEM{
groups: GROUP_ID -> USER_ID,
directories: DIRECTORY_ID -> one DIRECTORY,
files: FILE_ID -> one FILE
}{
}

sig PERMISSIONS{
owner: one USER_ID,
ownerPermissions: set PERMISSION,
group: lone GROUP_ID,
groupPermissions: set PERMISSION,
otherPermissions: set PERMISSION
}

sig DIRECTORY extends RESOURCE {
directoryId: one DIRECTORY_ID,
parentDirectory: one DIRECTORY,
subDirectories: set DIRECTORY,
files: set FILE_ID
}{
}

sig FILE extends RESOURCE {
fileId: FILE_ID,
contents: set CONTENT
}{
}

pred fileAccess(
user_in: USER_ID,
file_in: FILE_ID,
permissions_in: set PERMISSION
)
{
((SYSTEM.files[file_in].permissions).owner = user_in)
or
(
(user_in in SYSTEM.groups[SYSTEM.files[file_in].permissions.group])
and 
(all p : permissions_in | p in SYSTEM.files[file_in].permissions.groupPermissions)
)
or
(all p : permissions_in | p in SYSTEM.files[file_in].permissions.otherPermissions)
}

pred directoryAccess(
user_in: USER_ID,
directory_in: DIRECTORY_ID,
permissions_in: set PERMISSION
)
{
((SYSTEM.directories[directory_in].permissions).owner = user_in)
or
(
(user_in in SYSTEM.groups[SYSTEM.directories[directory_in].permissions.group])
and 
(all p : permissions_in | p in SYSTEM.directories[directory_in].permissions.groupPermissions)
)
or
(all p : permissions_in | p in SYSTEM.directories[directory_in].permissions.otherPermissions)
}

fun readFile
(
user_in: USER_ID,
file_in: FILE_ID
) : set CONTENT
{
fileAccess[user_in, file_in, READ]
=>
SYSTEM.files[file_in].contents
else none
}

fun readDirectory
(
user_in: USER_ID,
directory_in: DIRECTORY_ID
) : set FILE_ID
{
directoryAccess[user_in, directory_in, READ]
=>
SYSTEM.directories[directory_in].files
else none
}

pred writeFile
(
user_in: USER_ID,
file_in: FILE_ID,
content_in: CONTENT
)
{
fileAccess[user_in, file_in, WRITE]
=>
SYSTEM.files[file_in].contents = SYSTEM.files[file_in].contents + content_in
}

pred writeDirectory
(
user_in: USER_ID,
directory_in: DIRECTORY_ID,
fileId_in: FILE_ID
)
{
directoryAccess[user_in, directory_in, WRITE]
=>
SYSTEM.directories[directory_in].files = SYSTEM.directories[directory_in].files + fileId_in
else
SYSTEM.directories[directory_in].files = SYSTEM.directories[directory_in].files
}

pred executeFile
(
user_in: USER_ID,
file_in: FILE_ID
)
{
fileAccess[user_in, file_in, EXECUTE]
}

fun executeDirectory
(
user_in: USER_ID,
directory_in: DIRECTORY_ID
) : set FILE_ID
{
directoryAccess[user_in, directory_in, EXECUTE + READ]
=>
SYSTEM.directories[directory_in].files
else
none
}

run runAndVerifyDiscretionaryAccess

pred runAndVerifyDiscretionaryAccess() {
setupGroups
setupFiles
setupDirectories
verify
}

pred setupGroups() {
SYSTEM.groups = GROUP_1 -> (USER_1 + USER_2 + USER_3) + GROUP_2 -> (USER_4)
}

pred setupFiles() {
SYSTEM.files[FILE_1].permissions.owner = USER_1
SYSTEM.files[FILE_1].permissions.group = GROUP_1
SYSTEM.files[FILE_1].permissions.groupPermissions = (READ + WRITE)
SYSTEM.files[FILE_1].permissions.otherPermissions = (READ)
SYSTEM.files[FILE_1].contents = (CONTENT_1)

SYSTEM.files[FILE_2].permissions.owner = USER_2
SYSTEM.files[FILE_2].permissions.group = none
SYSTEM.files[FILE_2].permissions.groupPermissions = none
SYSTEM.files[FILE_2].permissions.otherPermissions = none
SYSTEM.files[FILE_2].contents = (CONTENT_2)
}

pred setupDirectories() {
SYSTEM.directories[DIRECTORY_1].permissions.owner = USER_1
SYSTEM.directories[DIRECTORY_1].permissions.group = GROUP_1
SYSTEM.directories[DIRECTORY_1].permissions.groupPermissions = (READ + WRITE + EXECUTE)
SYSTEM.directories[DIRECTORY_1].permissions.otherPermissions = none
SYSTEM.directories[DIRECTORY_1].files = (FILE_1)
}


pred verify() {

writeFile[USER_3, FILE_1, CONTENT_1]

readFile[USER_1, FILE_1] = (CONTENT_1)
readFile[USER_2, FILE_1] = (CONTENT_1)
readFile[USER_3, FILE_1] = (CONTENT_1)  
readFile[USER_4, FILE_1] = (CONTENT_1)
readFile[USER_5, FILE_1] = (CONTENT_1) 

readFile[USER_1, FILE_1] != (CONTENT_2)

writeFile[USER_2, FILE_2, CONTENT_2]

readFile[USER_1, FILE_2] = none
readFile[USER_2, FILE_2] = (CONTENT_2)
readFile[USER_3, FILE_2] = none
readFile[USER_4, FILE_2] = none
readFile[USER_5, FILE_2] = none

readFile[USER_2, FILE_2] != (CONTENT_1)

writeDirectory[USER_1, DIRECTORY_1, FILE_1]
writeDirectory[USER_2, DIRECTORY_1, FILE_1]
writeDirectory[USER_3, DIRECTORY_1, FILE_1]
writeDirectory[USER_4, DIRECTORY_1, FILE_1]
writeDirectory[USER_5, DIRECTORY_1, FILE_1]

readDirectory[USER_1, DIRECTORY_1] = FILE_1
readDirectory[USER_2, DIRECTORY_1] = FILE_1
readDirectory[USER_3, DIRECTORY_1] = FILE_1
readDirectory[USER_4, DIRECTORY_1] = none
readDirectory[USER_5, DIRECTORY_1] = none

executeFile[USER_1, FILE_1]
not executeFile[USER_2, FILE_1]
not executeFile[USER_3, FILE_1]
not executeFile[USER_4, FILE_1]
not executeFile[USER_5, FILE_1]

not executeFile[USER_1, FILE_2]
executeFile[USER_2, FILE_2]
not executeFile[USER_3, FILE_2]
not executeFile[USER_4, FILE_2]
not executeFile[USER_5, FILE_2]

executeDirectory[USER_1, DIRECTORY_2] = FILE_1
executeDirectory[USER_2, DIRECTORY_2] = FILE_1
executeDirectory[USER_3, DIRECTORY_2] = FILE_1
executeDirectory[USER_4, DIRECTORY_2] = none
executeDirectory[USER_5, DIRECTORY_2] = none
}
