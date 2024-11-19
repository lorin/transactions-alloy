open util/ordering[WriteNumber] as wo

sig Object {}

abstract sig Transaction {}

sig AbortedTransaction, CommittedTransaction extends Transaction {}


abstract sig Event {
    tr: Transaction,
    eo: set Event, // event order (partial ordering of events)
    tnext: lone Event // next event in the transaction
}

// Last event in a transaction
abstract sig FinalEvent extends Event {}

sig Commit extends FinalEvent {}

sig Abort extends FinalEvent {}

sig Write extends Event {
    obj: Object,
    wn : WriteNumber
}

sig Read extends Event {
    sees: Write // operation that did the write
}

sig WriteNumber {}


// helper function that returns set of events associated with a transaction
fun events[t : Transaction] : set Event {
    tr.t
}

fact "all transactions contain exactly one final event" {
    all t : Transaction | one events[t] & FinalEvent
}

fact "nothing comes after a final event" {
    no FinalEvent.tnext
}

fact "committed transactions contain a commit" {
    all t : CommittedTransaction | some Commit & events[t]
}

fact "aborted transactions contain an abort" {
    all t : AbortedTransaction | some Abort & events[t]
}

check {no iden & ^tnext}
