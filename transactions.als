open util/relation

// transactions
abstract sig Tr {
    ops : set Op
}

// Operations, also known as Events
abstract sig Op {
    tr: Tr,
    eo: set Op, // event order (partial ordering of events)
    tn: lone Op // transaction-next (next op in transaction)
} {
    this in tr.ops // this op is in the operations of the transactions it is associated with
    one ~ops[this] // this op is associated with exactly one transaction
}

fact "event ordering" {
    partialOrder[eo, Op]

    // If an event rj (xi:m) exists in E, it is preceded by
    // wi (xi:m) in E.
    // sees goes in the opposite direction of execution order (read "sees" a write backwards in time)
    sees in ~eo
}

fact "transaction-next" {
    irreflexive[tn]

    // tn preserves the order of all events within a transaction
    tn in eo

    // every pair of ops in a transaction must be reachable via tn 
    // in one direction or the other
    all t : Tr, disj o1, o2: t.ops |
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