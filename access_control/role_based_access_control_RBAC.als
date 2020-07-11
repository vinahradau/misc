// formal model for role based access control (RBAC)
// can be verified and visualized using Alloy Tools GUI
// developed by Serge (vinahradau@yahoo.de)

module RoleBasedAccessConrol

enum METADATA {CUSTOMER_NAME, CUSTOMER_ADDRESS, IS_VIP_CUSTOMER}

enum CONTENT {MUSTERMANN_1, MUSTERMANN_2, SEESTRASSE_1, SEESTRASSE_2, YES, NO}

enum USER {USER_1, USER_2, USER_3}

enum NODEID {NODE_1, NODE_2}

enum ROLE {ROLE_GUI_USER, ROLE_GUI_USER_FULL_ACCESS}

sig NODE {
nodeId: NODEID,
nodeDataContents: METADATA -> lone CONTENT
}

sig DOMAIN {
nodes: NODEID -> lone NODE,
roles: ROLE -> METADATA,
userAccessRights: USER -> ROLE
}{
}

pred StoreData
(d, d':DOMAIN,
nodeid_in: NODEID,
metadata_in: METADATA,
content_in: CONTENT)
{
d'.nodes[nodeid_in].nodeDataContents = d.nodes[nodeid_in].nodeDataContents ++ metadata_in -> content_in
}

pred AddRole
(d, d':DOMAIN,
role_in: ROLE,
metadata_in: set METADATA)
{
d'.roles = d.roles++ role_in -> metadata_in
}

pred AddUserAccessRight
(d, d':DOMAIN,
user_in: USER,
role_in: set ROLE)
{
d'.userAccessRights = d.userAccessRights ++ user_in -> role_in
}

fun accessData(
domain_in: DOMAIN, 
nodeid_in: NODEID,
user_in: USER, 
metadata_in: METADATA) : CONTENT
{
metadata_in in domain_in.roles[domain_in.userAccessRights[user_in]] => domain_in.nodes[nodeid_in].nodeDataContents[metadata_in]
else
none
}

run runAndVerifyRoleBasedAccessDomain for 1 DOMAIN, 2 NODE

pred runAndVerifyRoleBasedAccessDomain() {

setupNodes
assertNodes

setupUserAccess
assertUserAccess

assertAccessData
}


pred setupNodes() {
#DOMAIN.nodes = 2

DOMAIN.nodes[NODE_1].nodeId = NODE_1
DOMAIN.nodes[NODE_2].nodeId = NODE_2

StoreData[DOMAIN, DOMAIN, NODE_1, CUSTOMER_NAME, MUSTERMANN_1]
StoreData[DOMAIN, DOMAIN, NODE_1, CUSTOMER_ADDRESS, SEESTRASSE_1]
StoreData[DOMAIN, DOMAIN, NODE_1, IS_VIP_CUSTOMER, YES]

StoreData[DOMAIN, DOMAIN, NODE_2, CUSTOMER_NAME, MUSTERMANN_2]
StoreData[DOMAIN, DOMAIN, NODE_2, CUSTOMER_ADDRESS, SEESTRASSE_2]
StoreData[DOMAIN, DOMAIN, NODE_2, IS_VIP_CUSTOMER, NO]
}

pred assertNodes() {
DOMAIN.nodes[NODE_1].nodeDataContents[CUSTOMER_NAME] = MUSTERMANN_1
DOMAIN.nodes[NODE_1].nodeDataContents[CUSTOMER_ADDRESS] = SEESTRASSE_1
DOMAIN.nodes[NODE_1].nodeDataContents[IS_VIP_CUSTOMER] = YES

DOMAIN.nodes[NODE_2].nodeDataContents[CUSTOMER_NAME] = MUSTERMANN_2
DOMAIN.nodes[NODE_2].nodeDataContents[CUSTOMER_ADDRESS] = SEESTRASSE_2
DOMAIN.nodes[NODE_2].nodeDataContents[IS_VIP_CUSTOMER] = NO
}

pred setupUserAccess() {
AddRole[DOMAIN, DOMAIN, ROLE_GUI_USER, (CUSTOMER_NAME + IS_VIP_CUSTOMER)]
AddRole[DOMAIN, DOMAIN, ROLE_GUI_USER_FULL_ACCESS, (CUSTOMER_NAME + CUSTOMER_ADDRESS + IS_VIP_CUSTOMER)]

AddUserAccessRight[DOMAIN, DOMAIN, USER_1, (ROLE_GUI_USER_FULL_ACCESS)]
AddUserAccessRight[DOMAIN, DOMAIN, USER_2, (ROLE_GUI_USER)]
}

pred assertUserAccess() {
DOMAIN.roles[ROLE_GUI_USER_FULL_ACCESS] = CUSTOMER_NAME + CUSTOMER_ADDRESS + IS_VIP_CUSTOMER
DOMAIN.roles[ROLE_GUI_USER] = CUSTOMER_NAME + IS_VIP_CUSTOMER
DOMAIN.userAccessRights[USER_1] = ROLE_GUI_USER_FULL_ACCESS
DOMAIN.userAccessRights[USER_2] = ROLE_GUI_USER
DOMAIN.userAccessRights[USER_3] = none
}

pred assertAccessData() {
accessData[DOMAIN, NODE_1, USER_1, CUSTOMER_NAME] = MUSTERMANN_1
accessData[DOMAIN, NODE_1, USER_1, CUSTOMER_ADDRESS] = SEESTRASSE_1
accessData[DOMAIN, NODE_1, USER_1, IS_VIP_CUSTOMER] = YES

accessData[DOMAIN, NODE_1, USER_2, CUSTOMER_NAME] = MUSTERMANN_1
accessData[DOMAIN, NODE_1, USER_2, CUSTOMER_ADDRESS] = none // USER_2 has no access rights for this data
accessData[DOMAIN, NODE_1, USER_2, IS_VIP_CUSTOMER] = YES

accessData[DOMAIN, NODE_2, USER_1, CUSTOMER_NAME] = MUSTERMANN_2
accessData[DOMAIN, NODE_2, USER_1, CUSTOMER_ADDRESS] = SEESTRASSE_2
accessData[DOMAIN, NODE_2, USER_1, IS_VIP_CUSTOMER] = NO

accessData[DOMAIN, NODE_2, USER_2, CUSTOMER_NAME] = MUSTERMANN_2
accessData[DOMAIN, NODE_2, USER_2, CUSTOMER_ADDRESS] = none
accessData[DOMAIN, NODE_2, USER_2, IS_VIP_CUSTOMER] = NO

accessData[DOMAIN, NODE_1, USER_3, CUSTOMER_NAME] = none // USER_3 has no access rights
accessData[DOMAIN, NODE_1, USER_3, CUSTOMER_ADDRESS] = none
accessData[DOMAIN, NODE_1, USER_3, IS_VIP_CUSTOMER] = none

accessData[DOMAIN, NODE_2, USER_3, CUSTOMER_NAME] = none
accessData[DOMAIN, NODE_2, USER_3, CUSTOMER_ADDRESS] = none
accessData[DOMAIN, NODE_2, USER_3, IS_VIP_CUSTOMER] = none
}
