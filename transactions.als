open util/relation

// transactions
abstract sig Transaction {
    ops : set Op
}


// committed transactions
sig T extends Transaction {} {
    Commit in ops
}

// aborted transactions
sig A extends Transaction {} {
    Abort in ops
}

// Operations, also known as Events
abstract sig Op {
    tr: Transaction,
    eo: set Op, // event order (partial ordering of events)
    tn: lone Op // transaction-next (next op in transaction)
} {
    this in tr.ops // this op is in the operations of the transactions it is associated with
    one ~ops[this] // this op is associated with exactly one transaction
}

sig Commit extends Op {}

sig Abort extends Op {}

// commit and abort
fact {
    // all transactions contain a commit or an abort
    all t : Transaction | one t.ops & (Commit + Abort)

    // no transactions contain both a commit and abort
    no t : Transaction | Commit in t.ops and Abort in t.ops

    // commits and aborts come last
    no Commit.tn
    no Abort.tn
}

// See 4.2: Transaction histoires
fact "event ordering" {
    partialOrder[eo, Op]

    // If an event rj (xi:m) exists in E, it is preceded by wi (xi:m) in E.
    // Note: sees points in the opposite direction of event order (sees points backwards in time, eo points forward)
    sees in ~eo

    // If an event wi (xi:m) is followed by ri (xj ) without an
    // intervening event wi (xi:n) in E, xj must be xi:m. This
    // condition ensures that if a transaction modifies object
    // x and later reads x, it will observe its last update to x.
    all tr : Transaction, wr : Wr & tr.ops, rd : Rd & tr.ops |
        ((wr->rd in eo) and (no ww : Wr & tr.ops | (wr->ww + ww->rd) in eo)) => rd.sees = wr
}

fact "transaction-next" {
    irreflexive[tn]

    // Section 4.2:
    // It preserves the order of all events within a transaction
    // including the commit and abort events
    tn in eo

    // every pair of ops in a transaction must be reachable via tn 
    // in one direction or the other
    all t : Transaction, disj o1, o2: t.ops |
        o1->o2 in ^tn + ^~tn
}


// read-write operations
abstract sig RWOp extends Op {
    obj: Obj,
    val: Val
}

// writes
sig Wr extends RWOp {}

// reads
sig Rd extends RWOp {
    sees: Wr
} {
    obj = sees.@obj
    val = sees.@val
}


sig Obj {}

sig Val {}

run {some eo} for 6