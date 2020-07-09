module RoleBasedAccessConrol

enum METADATA {CUSTOMER_NAME, CUSTOMER_ADDRESS, IS_VIP_CUSTOMER}

enum ENTITY {ENTITY1, ENTITY2, ENTITY3}

enum CONTENT {MUSTERMANN, SEESTRASSE, YES, NO, XXXXX}

enum USER {USER1, USER2, USER3, USER4, USER5}

enum NODEID {NODE1, NODE2, NODE3}

enum ROLE {ROLE_GUI_USER, ROLE_GUI_USER_FULL_ACCESS}

sig NODE {
nodeId: NODEID,
nodeDataContents: METADATA -> lone CONTENT
}

sig DOMAIN {
nodes: NODEID -> lone NODE,
teams: ENTITY -> USER,
roles: ROLE -> METADATA,
userAccessRights: USER -> ROLE,
cidStoringNodesIds: set NODEID,
cidBulkAccessLog: USER -> NODEID
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

pred AddUser
(d, d':DOMAIN,
user_in: USER,
entity_in: ENTITY)
{
d'.teams = d.teams ++ entity_in -> user_in
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

run runAndVerifyDomain for 1 DOMAIN, 2 NODE

pred runAndVerifyDomain() {

setupNodes
assertNodes

setupUserAccess
assertUserAccess

assertAccessData
}


pred setupNodes() {
#DOMAIN.nodes = 2

DOMAIN.nodes[NODE1].nodeId = NODE1
DOMAIN.nodes[NODE2].nodeId = NODE2

StoreData[DOMAIN, DOMAIN, NODE1, CUSTOMER_NAME, MUSTERMANN]
StoreData[DOMAIN, DOMAIN, NODE1, CUSTOMER_ADDRESS, SEESTRASSE]
StoreData[DOMAIN, DOMAIN, NODE1, IS_VIP_CUSTOMER, YES]

StoreData[DOMAIN, DOMAIN, NODE2, CUSTOMER_NAME, MUSTERMANN]
StoreData[DOMAIN, DOMAIN, NODE2, CUSTOMER_ADDRESS, SEESTRASSE]
StoreData[DOMAIN, DOMAIN, NODE2, IS_VIP_CUSTOMER, NO]
}

pred assertNodes() {
DOMAIN.nodes[NODE1].nodeDataContents[CUSTOMER_NAME] = MUSTERMANN
DOMAIN.nodes[NODE1].nodeDataContents[CUSTOMER_ADDRESS] = SEESTRASSE
DOMAIN.nodes[NODE1].nodeDataContents[IS_VIP_CUSTOMER] = YES

DOMAIN.nodes[NODE2].nodeDataContents[CUSTOMER_NAME] = MUSTERMANN
DOMAIN.nodes[NODE2].nodeDataContents[CUSTOMER_ADDRESS] = SEESTRASSE
DOMAIN.nodes[NODE2].nodeDataContents[IS_VIP_CUSTOMER] = NO
}

pred setupUserAccess() {
AddUser[DOMAIN, DOMAIN, (USER1 + USER2 + USER5), ENTITY2]

AddRole[DOMAIN, DOMAIN, ROLE_GUI_USER, (CUSTOMER_NAME + IS_VIP_CUSTOMER)]
AddRole[DOMAIN, DOMAIN, ROLE_GUI_USER_FULL_ACCESS, (CUSTOMER_NAME + CUSTOMER_ADDRESS + IS_VIP_CUSTOMER)]

AddUserAccessRight[DOMAIN, DOMAIN, USER1, (ROLE_GUI_USER_FULL_ACCESS)]
AddUserAccessRight[DOMAIN, DOMAIN, USER2, (ROLE_GUI_USER)]
}

pred assertUserAccess() {
DOMAIN.roles[ROLE_GUI_USER_FULL_ACCESS] = CUSTOMER_NAME + CUSTOMER_ADDRESS + IS_VIP_CUSTOMER
DOMAIN.roles[ROLE_GUI_USER] = CUSTOMER_NAME + IS_VIP_CUSTOMER
DOMAIN.userAccessRights[USER1] = ROLE_GUI_USER_FULL_ACCESS + ROLE_BULK
DOMAIN.userAccessRights[USER2] = ROLE_GUI_USER + ROLE_BULK
DOMAIN.userAccessRights[USER3] = none
}

pred assertAccessData() {
accessData[DOMAIN, NODE1, USER1, CUSTOMER_NAME] = MUSTERMANN
accessData[DOMAIN, NODE1, USER1, CUSTOMER_ADDRESS] = SEESTRASSE
accessData[DOMAIN, NODE1, USER1, IS_VIP_CUSTOMER] = YES
accessData[DOMAIN, NODE1, USER2, CUSTOMER_NAME] = MUSTERMANN
accessData[DOMAIN, NODE1, USER2, CUSTOMER_ADDRESS] = none

accessData[DOMAIN, NODE1, USER2, IS_VIP_CUSTOMER] = YES

accessData[DOMAIN, NODE2, USER3, CUSTOMER_NAME] = none
accessData[DOMAIN, NODE2, USER3, CUSTOMER_ADDRESS] = none
accessData[DOMAIN, NODE2, USER3, IS_VIP_CUSTOMER] = none
}
