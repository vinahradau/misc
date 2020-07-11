// formal model for mandatory access control (MAC)
// can be verified and visualized using Alloy Tools GUI
// developed by Serge (vinahradau@yahoo.de)

module MandatoryAccessControl

enum DATA_CONFIDENTIALIY_LEVEL {TOPSECRET, SECRET, CONFIDENTIAL, UNCLASSIFIED}

enum USER_ID {USER_1, USER_2, USER_3, USER_4}

enum DOCUMENT_ID {DOCUMENT_1, DOCUMENT_2, DOCUMENT_3, DOCUMENT_4, DOCUMENT_5}

fun confidentialityOrdinal(
input: DATA_CONFIDENTIALIY_LEVEL
) : Int
{
input = TOPSECRET => 1
else
input = SECRET => 2
else
input = CONFIDENTIAL => 3
else
input = UNCLASSIFIED => 4
else
none
}

pred confidentialityCleared(
level1: DATA_CONFIDENTIALIY_LEVEL,
level2: DATA_CONFIDENTIALIY_LEVEL
)
{
confidentialityOrdinal[level1] =< confidentialityOrdinal[level2]
}

sig DOMAIN
{
documentClassification: DOCUMENT_ID -> lone DATA_CONFIDENTIALIY_LEVEL,
userClearance: USER_ID -> lone DATA_CONFIDENTIALIY_LEVEL
}

// all users have to have a clearance
// all documents have to have a classification
assert{
all d : DOCUMENT_ID | d in DOMAIN.documentClassification.univ
all u : USER_ID | u in DOMAIN.userClearance.univ
}

pred userDocumentAccessCleared(
user_in: USER_ID,
document_in: DOCUMENT_ID
)
{
confidentialityCleared[DOMAIN.userClearance[user_in], DOMAIN.documentClassification[document_in]]
}

run runAndVerifyMandatoryAccessDomain

pred runAndVerifyMandatoryAccessDomain() {
verifyConfidentialityHigherOrEqual

setupUsers
setupDocuments
verifyAccess
}

pred verifyConfidentialityHigherOrEqual() {
confidentialityCleared[TOPSECRET, TOPSECRET]
confidentialityCleared[TOPSECRET, SECRET]
confidentialityCleared[TOPSECRET, CONFIDENTIAL]
confidentialityCleared[TOPSECRET, UNCLASSIFIED]

confidentialityCleared[SECRET, SECRET]
confidentialityCleared[SECRET, CONFIDENTIAL]
confidentialityCleared[SECRET, UNCLASSIFIED]

confidentialityCleared[CONFIDENTIAL, CONFIDENTIAL]
confidentialityCleared[CONFIDENTIAL, UNCLASSIFIED]

not confidentialityCleared[SECRET, TOPSECRET]
not confidentialityCleared[CONFIDENTIAL, TOPSECRET]
not confidentialityCleared[UNCLASSIFIED, TOPSECRET]

not confidentialityCleared[CONFIDENTIAL, SECRET]
not confidentialityCleared[UNCLASSIFIED, SECRET]

not confidentialityCleared[UNCLASSIFIED, CONFIDENTIAL]
}

pred setupUsers() {
DOMAIN.userClearance[USER_1] = TOPSECRET
DOMAIN.userClearance[USER_2] = SECRET
DOMAIN.userClearance[USER_3] = CONFIDENTIAL
DOMAIN.userClearance[USER_4] = UNCLASSIFIED
}

pred setupDocuments() {
DOMAIN.documentClassification[DOCUMENT_1] = TOPSECRET
DOMAIN.documentClassification[DOCUMENT_2] = SECRET
DOMAIN.documentClassification[DOCUMENT_3] = CONFIDENTIAL
DOMAIN.documentClassification[DOCUMENT_4] = UNCLASSIFIED
}

pred verifyAccess() {
userDocumentAccessCleared[USER_1, DOCUMENT_1]
userDocumentAccessCleared[USER_1, DOCUMENT_2]
userDocumentAccessCleared[USER_1, DOCUMENT_3]
userDocumentAccessCleared[USER_1, DOCUMENT_4]

not userDocumentAccessCleared[USER_2, DOCUMENT_1]
userDocumentAccessCleared[USER_2, DOCUMENT_2]
userDocumentAccessCleared[USER_2, DOCUMENT_3]
userDocumentAccessCleared[USER_2, DOCUMENT_4]

not userDocumentAccessCleared[USER_3, DOCUMENT_1]
not userDocumentAccessCleared[USER_3, DOCUMENT_2]
userDocumentAccessCleared[USER_3, DOCUMENT_3]
userDocumentAccessCleared[USER_3, DOCUMENT_4]

not userDocumentAccessCleared[USER_4, DOCUMENT_1]
not userDocumentAccessCleared[USER_4, DOCUMENT_2]
not userDocumentAccessCleared[USER_4, DOCUMENT_3]
userDocumentAccessCleared[USER_4, DOCUMENT_4]
}
