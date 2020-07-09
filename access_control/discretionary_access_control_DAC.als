// decentralized
// Disscretionary Access Control (DAC)

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
group: one GROUP_ID,
groupPermissions: set PERMISSION,
otherPermissions: set PERMISSION
}

sig DIRECTORY extends RESOURCE {
directoryId: one DIRECTORY_ID,
directories: set DIRECTORY,
files: set FILE_ID
}{
}

sig FILE extends RESOURCE {
fileId: FILE_ID,
contents: set CONTENT
}{
}

fun readFile
(
user_in: USER_ID,
fileId_in: FILE_ID
) : set CONTENT
{
(
((SYSTEM.files[fileId_in].permissions).owner = user_in)
or
(user_in in SYSTEM.groups[SYSTEM.files[fileId_in].permissions.group] 
and 
READ in SYSTEM.files[fileId_in].permissions.groupPermissions)
or
(READ in SYSTEM.files[fileId_in].permissions.otherPermissions)
)
=>
SYSTEM.files[fileId_in].contents
else none
}

fun readDirectory
(
user_in: USER_ID,
directory_in: DIRECTORY_ID
) : set FILE_ID
{
(
((SYSTEM.directories[directory_in].permissions).owner = user_in)
or
(user_in in SYSTEM.groups[SYSTEM.directories[directory_in].permissions.group] 
and 
READ in SYSTEM.directories[directory_in].permissions.groupPermissions)
or
(READ in SYSTEM.directories[directory_in].permissions.otherPermissions)
)
=>
SYSTEM.directories[directory_in].files
else none
}

pred writeFile
(
user_in: USER_ID,
fileId_in: FILE_ID,
content_in: CONTENT
)
{
((SYSTEM.files[fileId_in].permissions).owner = user_in)
or
(
user_in in SYSTEM.groups[SYSTEM.files[fileId_in].permissions.group] 
and 
WRITE in SYSTEM.files[fileId_in].permissions.groupPermissions
)
or
(
WRITE in SYSTEM.files[fileId_in].permissions.otherPermissions
)
=>
SYSTEM.files[fileId_in].contents = SYSTEM.files[fileId_in].contents + content_in
}

pred writeDirectory
(
user_in: USER_ID,
directory_in: DIRECTORY_ID,
fileId_in: FILE_ID
)
{
(
((SYSTEM.directories[directory_in].permissions).owner = user_in)
or
(
user_in in SYSTEM.groups[SYSTEM.directories[directory_in].permissions.group] 
and 
WRITE in SYSTEM.directories[directory_in].permissions.groupPermissions
)
or
(WRITE in SYSTEM.directories[directory_in].permissions.otherPermissions)
)
=>
SYSTEM.directories[directory_in].files = SYSTEM.directories[directory_in].files + fileId_in
else
SYSTEM.directories[directory_in].files = SYSTEM.directories[directory_in].files
}

pred executeFile
(
user_in: USER_ID,
fileId_in: FILE_ID
)
{
((SYSTEM.files[fileId_in].permissions).owner = user_in)
or
(
user_in in SYSTEM.groups[SYSTEM.files[fileId_in].permissions.group] 
and 
EXECUTE in SYSTEM.files[fileId_in].permissions.groupPermissions
)
or
(
EXECUTE in SYSTEM.files[fileId_in].permissions.otherPermissions
)
}

fun executeDirectory
(
user_in: USER_ID,
directoryId_in: DIRECTORY_ID
) : set FILE_ID
{
(
((SYSTEM.directories[directoryId_in].permissions).owner = user_in)
or
(
user_in in SYSTEM.groups[SYSTEM.directories[directoryId_in].permissions.group] 
and 
EXECUTE in SYSTEM.directories[directoryId_in].permissions.groupPermissions
and
READ in SYSTEM.directories[directoryId_in].permissions.groupPermissions
)
or
(
EXECUTE in SYSTEM.directories[directoryId_in].permissions.otherPermissions
and
READ in SYSTEM.directories[directoryId_in].permissions.otherPermissions
)
)
=>
SYSTEM.directories[directoryId_in].files
else
none
}

run runAndVerify

pred runAndVerify() {
setupFiles
verify
}

pred setupFiles() {
SYSTEM.groups = GROUP_1 -> (USER_1 + USER_2 + USER_3) + GROUP_2 -> (USER_4)

SYSTEM.files[FILE_1].permissions.owner = USER_1
SYSTEM.files[FILE_1].permissions.group = GROUP_1
SYSTEM.files[FILE_1].permissions.groupPermissions = (READ + WRITE)
SYSTEM.files[FILE_1].permissions.otherPermissions = (READ)
SYSTEM.files[FILE_1].contents = (CONTENT_1)

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

executeDirectory[USER_1, DIRECTORY_2] = FILE_1
executeDirectory[USER_2, DIRECTORY_2] = FILE_1
executeDirectory[USER_3, DIRECTORY_2] = FILE_1
executeDirectory[USER_4, DIRECTORY_2] = none
executeDirectory[USER_5, DIRECTORY_2] = none
}
