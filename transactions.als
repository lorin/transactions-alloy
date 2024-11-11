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
    some ww
    some P.eval
    some PRead
}

pred multiple_writes {
    no A
    one T
    #Wr > 1
}

pred deps {
    some ww
    some T <: wr
    some rw
}

run runner for 8 // but exactly 2 T
// run multiple_writes for 6 // but exactly 2 T
// run deps for 8 but exactly 4 T

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
sig T extends Transaction {
    ww : set T, // directly write-depends

    iwr : set T, // directly item-read-depends
    pwr : set T, // directly predicate-read-depends
    wr : set T, // directly read-depends
    irw : set T, // directly item-anti-depends
    prw : set T, // directly directly predicate-anti-depends
    rw : set T, // directly anti-depends
} 


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

// object versions
sig OV {
    obj : Obj,
    tr: T,
    v: V
}

sig Vset {
    ovs : set OV
}

sig P {
    eval : Vset -> set Obj
}

// Predicate read
sig PRead extends Op {
    vset : Vset,
    p: P,
    objs : set Obj
}

fact "predicate read is consistent with predicate" {
    all pread : PRead | pread.p.eval[pread.vset] = pread.objs
}

fact "object versions are unique" {
    no disj ov1, ov2 : OV | {
        ov1.obj = ov2.obj
        ov1.tr = ov2.tr
        ov1.v = ov2.v
    }
}

fact "object versions must correpsond to a write" {
    all ov : OV | some wr : Wr | {
        ov.obj = wr.obj
        ov.tr = wr.tr
        ov.v = wr.v
    }
}

fact "Vsets are complete" {
    all vset : Vset | 
        Obj in vset.ovs.obj
}

fact "only one version per object in a vset" {
    all vset : Vset | no disj ov1, ov2 : vset.ovs | 
        ov1.obj = ov2.obj
}

fact "Vsets are unique" {
    no disj vset1, vset2 : Vset | vset1.ovs = vset2.ovs
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

fact "installed version is always last commit" {
    all t : T, wr : t.ops & Wr |
        (some wr.installs) => (no ww : wr.(^tn) & Wr | ww.obj = wr.obj)
}

fact "if a read sees a write in the same transaction, it must be the most recent one" {
    all t : Transaction, rd : t.ops & Rd | 
        (rd.sees in t.ops) => no wr : t.ops & Wr | {
            rd.obj = wr.obj
            // wr is before rd 
            wr in rd.^~tn

            // wr is after the seen write (rd.sees)
            wr in rd.sees.^tn
        }
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

fact "cvn relations must be associated with the object" {
    all o : Obj |  {
        no o.cvn.CV.obj - o
        no o.cvn[CV].obj - o
    }
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

fact DirectlyWriteDepends {
    irreflexive[ww]

    all disj Ti, Tj : T | Ti->Tj in ww => 
        some cv1 : Ti.ops.installs, cv2 : Tj.ops.installs | {
            cv1.obj = cv2.obj
            cv1.tr = Ti
            cv2.tr = Tj
            cv1->cv2 in vn
        }
}

fact DirectlyReadDepends {
    wr = iwr + pwr
}


/*
We say that Tj directly item-read-depends on Ti if Ti installs some object version
xi and Tj reads xi
*/
fact DirectlyItemReadDepends {
    irreflexive[iwr]

    all disj Ti, Tj : T | Ti->Tj in iwr => 
        some cv : Ti.ops.installs, rd : Rd & Tj.ops {
            rd.sees = cv.wr
        }
}

fact DirectlyAntiDepends {
    rw = irw + prw
}

// True if transaction T has a read that corresponds to this committed version
pred reads[t : Transaction, cv: CV] {
    some rd : t.ops & Rd | rd.sees.installs = cv
}


/*
Directly item-anti-depends: We say that Tj directly item-anti-depends on
transaction Ti if Ti reads some object version xk and Tj installs x’s next
version (after xk ) in the version order. Note that the transaction that wrote
the later version directly item-anti-depends on the transaction that read the
earlier version
*/
fact DirectlyItemAntiDepends {
    irreflexive[irw]
    all disj Ti, Tj : T | Ti->Tj in irw =>
        some xk : CV | {
            // Ti reads xk
            reads[Ti, xk]

            // Tj modifies the next version of xk
            xk.vn.tr = Tj
        }
}

fact DirectlyPredicateReadDepends {
    // TODO: implement this
    no pwr
}

fact DirectlyPredicateAntiDepends {
    // TODO implement this
    no prw
}