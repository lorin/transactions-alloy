
// transactions
abstract sig Tr {
    ops : set Op
}

// Operations
abstract sig Op {
    tr: Tr,
    eo: set Op, // event order (partial ordering of events)
    tn: lone Op // transaction-next (next op in transaction)
} {
    this in tr.ops // this op is in the operations of the transactions it is associated with
    one ~ops[this] // this op is associated with exactly one transaction
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

run {}