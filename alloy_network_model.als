// a network Alloy model with members, friendships, posts and likes

module Friends

sig Friends{
members: set Member,
likes: Likable -> Member,
friendship: Member -> Member
}

sig Member{
}

sig Text{
}

abstract sig Likable{
author: one Member 
}

sig Photo extends Likable{
caption: one Text,
post: lone Post 
}

sig Post extends Likable{
text: one Text,
photo: set Photo
}

pred isGroup(m1, m2: Member){
isGroup[m1 + m2]
}

pred isGroup(members: set Member){ // two members are in a group if they are friends (directly or indirectly) or like each other's posts
all m1 : members | all m2 : members | (m1 -> m2 in ^(Friends.friendship) or m2 -> m1 in ^(Friends.friendship)) 
or (some l : Likable | (l.author = m1 and l -> m2 in Friends.likes) or (l.author = m2 and l -> m1 in Friends.likes))
or (m1 = m2)
}

fact{
not isGroup[Friends.members] // not all members are in agroup
all t : Text | all p1 : Photo | all p2 : Photo | t = p1.caption and t = p2.caption => p1 = p2 
all t : Text | all p1 : Post | all p2 : Post | t = p1.text and t = p2.text => p1 = p2 
all t : Text | all p1 : Photo | all p2 : Post | t = p1.caption => t != p2.text 
all m : Member | m -> m not in Friends.friendship
all m : (Friends.friendship).univ | m in Friends.members
all m : univ.(Friends.friendship) | m in Friends.members
all l : Likable | l.author not in Friends.likes[l] 
}

pred like(friends: Friends, member: Member, likable: Likable){
friends.likes = friends.likes ++ likable -> member 
}

pred addFriends(friends: Friends, m1, m2 : Member){
friends.friendship = friends.friendship ++ m1 -> m2 
}

run like for 5 Friends, 5 Text, 5 Member, 5 Photo, 5 Post
