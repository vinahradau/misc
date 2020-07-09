module MandatoryAccessControl

enum DATA_CONFIDENTIALIY_LEVEL {TOPSECRET, SECRET, CONFIDENTIAL, UNCLASSIFIED}

enum USER_ID {USER_1, USER_2, USER_3, USER_4, USER_5}

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

pred confidentialityHigherOrEqual(
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

pred cleared(
user_in: USER_ID,
document_in: DOCUMENT_ID
)
{
confidentialityHigherOrEqual[DOMAIN.userClearance[user_in], DOMAIN.documentClassification[document_in]]
}

run runAndVerify

pred runAndVerify() {
verifyConfidentialityHigherOrEqual

setupUsers
setupDocuments
verifyAccess
}

pred verifyConfidentialityHigherOrEqual() {
confidentialityHigherOrEqual[TOPSECRET, TOPSECRET]
confidentialityHigherOrEqual[TOPSECRET, SECRET]
confidentialityHigherOrEqual[TOPSECRET, CONFIDENTIAL]
confidentialityHigherOrEqual[TOPSECRET, UNCLASSIFIED]

confidentialityHigherOrEqual[SECRET, SECRET]
confidentialityHigherOrEqual[SECRET, CONFIDENTIAL]
confidentialityHigherOrEqual[SECRET, UNCLASSIFIED]

confidentialityHigherOrEqual[CONFIDENTIAL, CONFIDENTIAL]
confidentialityHigherOrEqual[CONFIDENTIAL, UNCLASSIFIED]

not confidentialityHigherOrEqual[SECRET, TOPSECRET]
not confidentialityHigherOrEqual[CONFIDENTIAL, TOPSECRET]
not confidentialityHigherOrEqual[UNCLASSIFIED, TOPSECRET]

not confidentialityHigherOrEqual[CONFIDENTIAL, SECRET]
not confidentialityHigherOrEqual[UNCLASSIFIED, SECRET]

not confidentialityHigherOrEqual[UNCLASSIFIED, CONFIDENTIAL]
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
cleared[USER_1, DOCUMENT_1]
cleared[USER_1, DOCUMENT_2]
cleared[USER_1, DOCUMENT_3]
cleared[USER_1, DOCUMENT_4]

not cleared[USER_2, DOCUMENT_1]
cleared[USER_2, DOCUMENT_2]
cleared[USER_2, DOCUMENT_3]
cleared[USER_2, DOCUMENT_4]

not cleared[USER_3, DOCUMENT_1]
not cleared[USER_3, DOCUMENT_2]
cleared[USER_3, DOCUMENT_3]
cleared[USER_3, DOCUMENT_4]

not cleared[USER_4, DOCUMENT_1]
not cleared[USER_4, DOCUMENT_2]
not cleared[USER_4, DOCUMENT_3]
cleared[USER_4, DOCUMENT_4]
}
