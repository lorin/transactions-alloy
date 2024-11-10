open util/relation
open util/ordering[V] as vo

one sig X,Y extends Obj {}

pred runner {
    // no Abort
    // some eo
    // some cvn
    // some CV
    no A
    some Rd
    some CV
    some cvn

}

run runner for 6 // but exactly 2 T

abstract sig Obj {
    // committed versions
    cvs : set CV,

    // "next" relation of committed versions
    cvn : CV lone -> lone CV
}

// transactions
abstract sig Transaction {
    ops : set Op
}

// committed transactions
sig T extends Transaction {} 


// aborted transactions
sig A extends Transaction {} 

// Operations, also known as Events
abstract sig Op {
    tr: Transaction,
    eo: set Op, // event order (partial ordering of events)
    tn: lone Op // transaction-next (next op in transaction)
}

sig Commit extends Op {}

sig Abort extends Op {}

// read-write operations
abstract sig RWOp extends Op {
    obj: Obj,
    v: V
}

// writes
sig Wr extends RWOp {
    installs : lone CV
}


pred first_write_of_obj[wr : Wr] {
    no ww : wr.^~tn & Wr | ww.obj = wr.obj
}

// reads
sig Rd extends RWOp {
    tw: Transaction,  // transaction that did the write
    sees: Wr // operation that did the write
} 

// versions
sig V {}

// committed versions
sig CV {
    obj: Obj,
    tr: T,
    wr: Wr,
    v: V,
    vn: lone CV // next-version
} 

fact OpStuff {
    all op : Op | {
        op in op.tr.ops // this op is in the operations of the transactions it is associated with
        one ~ops[op] // this op is associated with exactly one transaction
    }
}

fact "no empty transactions" {
    no t : Transaction | no t.ops - (Commit + Abort)
}

fact "commit and abort" {
    // all transactions contain a commit or an abort
    all t : Transaction | one t.ops & (Commit + Abort)

    // no transactions contain both a commit and abort
    no t : Transaction | some Commit & t.ops and some Abort & t.ops

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


fact CommittedVersionNextVersion {
    vn = Obj.cvn
}

fact CommittedTransaction {
    all t : T | some Commit & t.ops
}

fact AbortedTransaction {
    all t : A | some Abort & t.ops
}


fact InstallsCommittedVersion {
    installs = ~(CV <: wr)
}

fact OpStuff {
    all op : Op | {
        op in op.tr.ops // this op is in the operations of the transactions it is associated with
        one ~ops[op] // this op is associated with exactly one transaction
    }
}

fact "committed versions are associated with the object" {
    all o : Obj | o.cvs.obj in o
}

fact "writes must happen in version order" {
    // initial write is first version
    all t : Transaction, wr : t.ops & Wr |
        first_write_of_obj[wr] => wr.v = vo/first

    // next writes are always successive versions
    all t : Transaction, disj w1,w2 : t.ops & Wr |
        ((w1->w2 in ^tn) and (no w3: t.ops & Wr | (w1->w3 + w3->w2) in ^tn)) => w2.v = next[w1.v]
}

fact RdSees {
    all rd : Rd |  {
        rd.v = rd.sees.v // version read is same as verion written
        rd.obj = rd.sees.obj // object read is same as object written
        rd.sees.tr = rd.tw // seen write op belongs to transaction that does the write
    }
}

fact CommittedVersions {
    all cv : CV |  {
        cv in cv.obj.cvs
        cv.wr.v = cv.v
        cv.wr in cv.tr.ops
        cv.wr.obj = cv.obj
    }
}

fact "transaction can only commit one version" {
    all obj : Obj |
        no disj cv1, cv2 : obj.cvs |
            cv1.tr = cv2.tr
}

fact "CV-next relation" {
    all o : Obj | {
        irreflexive[o.cvn]
        totalOrder[*(o.cvn), o.cvs]
    }
}
