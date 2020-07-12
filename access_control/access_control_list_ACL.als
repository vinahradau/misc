// formal model for access control list (ACL)
// standard access control list, based on source ip address
// can be verified and visualized using Alloy Tools GUI
// developed by Serge (vinahradau@yahoo.de)

module AccessControlList

enum ROUTER_ID {ROUTER_1, ROUTER_2}

enum PACKAGE {PACKAGE_1, PACKAGE_2}

enum IP_ADDRESS {IP_ADDRESS_1, IP_ADDRESS_2, IP_ADDRESS_3, IP_ADDRESS_4, IP_ADDRESS_5, ANY}

enum MODE {PERMIT, DENY}

enum DIRECTION {IN, OUT}

enum ENTRY_ID {ENTRY_1, ENTRY_2, ENTRY_3}

sig ROUTER {
routerId: one ROUTER_ID,
ipAddress: one IP_ADDRESS,
accessList: one ACCESS_LIST,
packages: set PACKAGE
}

sig DOMAIN {
routers: ROUTER_ID -> lone ROUTER
}{
}

sig ACCESS_LIST {
entries: ENTRY_ID -> ACCESS_LIST_ENTRY
}{
}

sig ACCESS_LIST_ENTRY {
source: one IP_ADDRESS,
mode: one MODE,
direction: one DIRECTION,
}{
}

pred AddAccessListEntry
(routerId_in: ROUTER_ID,
entryId_in: ENTRY_ID,
source_in: IP_ADDRESS,
mode_in: MODE)
{
univ.((entryId_in <: DOMAIN.routers[routerId_in].accessList.entries)).source = source_in 
univ.((entryId_in <: DOMAIN.routers[routerId_in].accessList.entries)).mode = mode_in 
}

pred AcceptData
(
accessList_in: ACCESS_LIST,
ipAddress_in: IP_ADDRESS
)
{
(not #(accessList_in.entries) = 0)
and
(
one entry : univ.(accessList_in.entries) | (entry.source = ipAddress_in and entry.mode = PERMIT)
)
}

pred SendData
(source_in, destination_in: ROUTER_ID,
package_in: PACKAGE
)
{
AcceptData[DOMAIN.routers[destination_in].accessList, DOMAIN.routers[source_in].ipAddress] 
=> DOMAIN.routers[destination_in].packages = DOMAIN.routers[destination_in].packages + package_in
}

run runAndVerifyRoleBasedAccessDomain for 1 DOMAIN, 2 ROUTER, 2 ACCESS_LIST, 2 ACCESS_LIST_ENTRY 
pred runAndVerifyRoleBasedAccessDomain() {
setupRouters
assertRouters
}

pred setupRouters() {
#DOMAIN.routers = 2

DOMAIN.routers[ROUTER_1].routerId = ROUTER_1
DOMAIN.routers[ROUTER_2].routerId = ROUTER_2

DOMAIN.routers[ROUTER_1].ipAddress = IP_ADDRESS_1
DOMAIN.routers[ROUTER_2].ipAddress = IP_ADDRESS_2

AddAccessListEntry[ROUTER_1, ENTRY_1, IP_ADDRESS_2, DENY]
AddAccessListEntry[ROUTER_2, ENTRY_2, IP_ADDRESS_1, PERMIT]

#(DOMAIN.routers[ROUTER_1].accessList.entries) = 1
#(DOMAIN.routers[ROUTER_2].accessList.entries) = 1

SendData[ROUTER_1, ROUTER_2, PACKAGE_1]
SendData[ROUTER_2, ROUTER_1, PACKAGE_1]
}

pred assertRouters() {
PACKAGE_1 in DOMAIN.routers[ROUTER_2].packages
PACKAGE_1 not in DOMAIN.routers[ROUTER_1].packages
}
