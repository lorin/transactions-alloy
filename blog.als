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

run {}
