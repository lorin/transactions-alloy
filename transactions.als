open util/relation
open util/ordering[WriteNumber] as wo

run {some PredicateRead.objs; #Object>1} for 6

//
// signatures
//

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

abstract sig Predicate {}

abstract sig PredicateRead extends Event {
    p : Predicate,
    objs : set Object
}

sig WriteNumber {}


fun obj[] : Read -> Object {
    {r : Read, o : Object | o = r.sees.obj}
}

fun events[t : Transaction] : set Event {
    (Event <: tr).t
}


//
// Facts
//

// transactions


fact "all transactions contain exactly one final event" {
    all t : Transaction | one events[t] & FinalEvent
}

fact "nothing comes after a final event" {
    no FinalEvent.tnext
}

fact "committed transactions contain a commit" {
    all t : CommittedTransaction | some Commit & t.events
}

fact "aborted transactions contain an abort" {
    all t : AbortedTransaction | some Abort & t.events
}

fact "transactions must contain at least one event in addition to a final event" {
    no t : Transaction | no t.events - FinalEvent
}


// operation ordering

/**
 * 4.2: Transaction histoires
 * The partial order of events E in a history obeys the following constraints:
 */
fact "Event order (eo) is a partial order on operations" {
    partialOrder[eo, Event]
}

fact "eo preserves the order of all events within a transaction including the commit and abort events" {
    tnext in eo
}

fact "all events within a transaction are totally ordered" {
    all T : Transaction |  {
        totalOrder[eo, events[T]] // eo is totally ordered per transaction
        some e : events[T] | pred/totalOrder[events[T], e, tnext] // tnext generates a total ordering
    }
}


// write number

fact "write number is consistent with execution order" {
    all T : Transaction, disj w1, w2 : events[T] & Write |
        lt[w1.wn, w2.wn] <=> w1 -> w2 in eo
}

fact "first write is first write number" {
    all T : Transaction, w : events[T] & Write |
        no w.^~tnext => w.wn = first
}

fact "write number goes up one at a time" {
    all T : Transaction, disj w1, w2 : events[T] & Write | ({
        w1.obj = w2.obj
        w1 -> w2 in eo
        no w3 : events[T] & Write - (w1+w2) | w3.obj=w1.obj and (w1->w3 + w3->w2) in eo
    } => w1.wn.next = w2.wn)
}

// relationships between reads and writes

fact "If an event rj (xi:m) exists in E, it is preceded by wi (xi:m) in E" {
    // We model this with the "sees" relation.
    // If a read sees a write,
    // then it must precede the write.
    // Note: sees points in the opposite direction from eo
    sees in ~eo
}


/**
 * If an event wi (xi:m) is followed by ri (xj) without an intervening event wi (xi:n) in E, xj must be xi:m
 */
fact "transaction must read its own writes" {
    all T : Transaction, w : T.events & Write, r : T.events & Read | ({
            w.obj = r.obj
            w->r in eo
            no v : T.events & Write | v.obj = r.obj and (w->v + v->r) in eo
    } => r.sees = w)

}
