open util/relation
open util/ordering[VersionNumber] as vo

check PL1

abstract sig Object {
    vs : set Version,
    next : Version lone -> lone Version
}

abstract sig Transaction {
    ops : set Operation
}

sig CommittedTransaction extends Transaction {
    installs : set Version,

    ww : set CommittedTransaction, // directly write-depends

    iwr : set CommittedTransaction, // directly item-read-depends
    pwr : set CommittedTransaction, // directly predicate-read-depends
    wr : set CommittedTransaction, // directly read-depends
    irw : set CommittedTransaction, // directly item-anti-depends
    prw : set CommittedTransaction, // directly directly predicate-anti-depends
    rw : set CommittedTransaction, // directly anti-depends
}

sig AbortedTransaction extends Transaction {}


abstract sig Operation {
    tr: Transaction,
    eo: set Operation, // event order (partial ordering of events)
    tn: lone Operation // transaction-next (next op in transaction)
}



sig Commit extends Operation {}

sig Abort extends Operation {}

abstract sig ReadWriteOperation extends Operation {
    obj: Object,
    v: Version
}
sig Write extends ReadWriteOperation {
    installs : lone Version
}

sig Read extends ReadWriteOperation {
    tw: Transaction,  // transaction that did the write
    sees: Write // operation that did the write
}

sig VersionNumber {}


// installed (committed) versions
sig Version {
    obj: Object,
    tr: CommittedTransaction,
    wo: Write,
    i: VersionNumber,
    vn: lone Version // next-version
}

sig Vset {
    vs : set Version
}

sig Predicate {
    matches : set Version
}


sig PredicateRead extends Operation {
    vset : Vset,
    p: Predicate,
    vs : set Version
}

//
//
// Isolation levels
//
//


/**
 * We define PL-1 as the level in which G0 is disallowed
 */
assert PL1 {
    not G0
}

/**
 * We define isolation level PL-2 as one in which phenomenon G1 is disallowed
 */
assert PL2 {
    not G1
}

/*
 * We define level PL-2.99 as one that proscribes G1 and G2-item
 */
assert PL2_99 {
    not G1
    not G2item
}

/**
 * We define PL-3 as an isolation level that proscribes G1 and G2
 */
assert PL3 {
    not G1
    not G2
}


//
//
// Phenomena
//
//


/**
 * G0: Write Cycles. A history H exhibits phenomenon
 * G0 if DSG(H) contains a directed cycle consisting
 * entirely of write-dependency edges.
 */
pred G0 {
    not acyclic[ww, CommittedTransaction]
}

/**
 * Phenomenon G1 captures the essence of no-dirty-reads
 * and is comprised of G1a, G1b and G1c. 
 */
pred G1 {
    G1a or G1b or G1c
}

/**
 * G1a: Aborted Reads
 * 
 * A history H shows phenomenon G1a if it contains an aborted transaction T1 and a
 * committed transaction T2 such that T2 has read some object modified by T1
 * 
 */
pred G1a {
    some T1 : AbortedTransaction, T2 : CommittedTransaction, r : T2.ops & Read, w : T1.ops & Write | r.sees = w
}


/**
 * G1b: Intermediate Reads.
 * 
 * A history H shows phenomenon G1b if it contains a committed transaction
 * T2 that has read a version of object x written by transaction T1 that was not T1’s
 * final modification of x.
*/
pred G1b {
    some T1 : Transaction, T2 : CommittedTransaction, r : T2.ops & Read | let x = r.obj, wi=r.sees |
    {
        no T1 & T2 // different transactions
        wi.tr = T1
        some wj : (T1.ops - wi) & Write | {
            wj.obj = x
            wi->wj in eo
        }
    }
}

/**
 * G1c: Circular Information Flow.
 * 
 * A history H exhibits phenomenon G1c if DSG(H) contains a directed cycle
 * consisting entirely of dependency edges
 */
pred G1c {
    not acyclic[ww + wr, CommittedTransaction]
}

fun DSG[] : CommittedTransaction -> CommittedTransaction {
    ww + wr + rw
}

/**
 * G2: Anti-dependency Cycles. A history H exhibits
 * phenomenon G2 if DSG(H) contains a directed cycle
 * with one or more anti-dependency edges.
*/
pred G2 {
    // must contain a cycle
    not acyclic[DSG, CommittedTransaction]

    // must not contain a cycle if there are no antidependency edges
    acyclic[DSG - rw, CommittedTransaction]
}


/*
G2-item: Item Anti-dependency Cycles. A history H exhibits phenomenon G2-item if
DSG(H) contains a directed cycle having one or more item-antidependency edges.
*/
pred G2item {
    // must contain a cycle
    some iden & ^DSG

    // must not contain a cycle if there are no item-antidependency edges
    no iden & ^(DSG - irw)
}
