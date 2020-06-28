// Barber Paradox model with a solution
// Developed by Serge Vinahradau
// To tretrieve all self shaved persons, call selfShaved[] function
// To retrieve the barber, call the barber[] function


sig Person{
}

one sig Town{
  shaved: Person -> Person
}

pred shaves(
  barber: Person, 
  client: Person
){
  barber -> client in Town.shaved
}

fact{
// some barber : Person | all person : Person | /* no solution */
some barber : Person | all person : Person - barber | /* solution: exclude the barber from the universal quantifier set */
(shaves[barber, person] <=> not shaves[person, person])
}

pred isBarber[
p: Person
] {
p in (Town.shaved).univ
and
all s : univ.(p <: (Town.shaved - p -> p)) | s -> s not in Town.shaved
}

fun selfShaved[
]: set Person
{
{p : Person | p -> p in Town.shaved}
}

fun barber[
]: set Person
{
{p : Person | isBarber[p]}
}

run shaves for 1 Town, 5 Person
