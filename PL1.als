/*

Implements PL1.

Assumes all transactions commit, because write PL1 does not involve aborts.

Source: Generalized Isolation Level Definitions,
Atul Adya, Barbara Liskov, Patrick O'Neil. 
Proceedings of the IEEE International Conference on Data Engineering, March 2000.

*/
open util/ordering[Version] as vo
open util/ordering[Op] as oo

abstract sig Tr {
    // which transactions happened before this one
    precedes: set Tr,
    ops : set Op

}

// committed transactions
sig TrC extends Tr {}

// aborted transactions
sig TrA extends Tr {}

fact beforeIsAcyclic{
    no ^precedes & iden
}

abstract sig Op {
    tr: Tr,
    obj: Obj,
    val: Val
} {
    this in tr.ops
}

sig Wr extends Op {}

sig Rd extends Op {
    sees: Wr
} {
    obj = sees.@obj
    val = sees.@val
}


sig Obj {
    vers : set VersionedValue
} {
    // each version val is associated with a unique transaction
    no disj vv1, vv2 : vers | {
        vv1.tr = vv2.tr
    }

    // only one of each version
    no disj vv1, vv2 : vers | {
        vv1.v = vv2.v 
    }
}

sig VersionedValue {
    v : Version,
    val : Val,
    tr : TrC
}

fact VersionOrderRespectsbeforeibility {
    all obj : Obj |
        // It cannot be the case that:
        no disj vvi, vvj : obj.vers {
            // j is beforeible to i, meaning j precedes i
            vvj.tr in vvi.tr.precedes 

            // i's version is less than j's version, meaning i was written before j
            lt[vvi.v, vvj.v]
        }
}

/*
If there are two transactions that are not beforeible to each other,
they both cannot write to the same obj
*/
fact NoConcurrentWrites {
    no obj : Obj | some disj Ti, Tj : Tr | {
        Ti not in Tj.precedes
        Tj not in Ti.precedes
        some disj vv1, vv2 : obj.vers |  {
            vv1.tr = Ti
            vv2.tr = Tj
        }
    }
}

sig Val {}

sig Version {}

/*

Definition 6 : Directly Write-Depends. A transaction Tj
directly write-depends on Ti if Ti installs a version xi and
Tj installs x’s next version (after xi ) in the version order

Ti -> Tj

*/
fun ww[] : Tr -> Tr {
    { Ti: Tr, Tj: Tr  | some obj : Obj, vv1,vv2 : obj.vers | {
        vv1.tr = Ti
        vv2.tr = Tj
        next[vv1.v] = vv2.v }}
}

/*
G0: Write Cycles. A history H exhibits phenomenon
G0 if DSG(H) contains a directed cycle consisting
entirely of write-dependency edges.
*/
pred G0 {
    some iden & ^ww[]
}

/*
we define PL-1 as the level in which
G0 is disallowed
*/

assert PL1 {
    not G0
}

/*
G1a: Aborted Reads

A history H shows phenomenon G1a if it contains an aborted transaction T1 and a
committed transaction T2 such that T2 has read some object modified by T1

*/
pred G1a {
    some T1 : TrA, T2 : TrC, r : T2.ops & Rd, w : T1.ops & Wr | r.sees = w
}

/* 
G1b: Intermediate Reads. A history H shows phenomenon G1b if it contains a committed transaction
T2 that has read a version of object x  written by transaction T1 that was not T1’s
final modification of x.
*/
pred G1b {
    some disj T1, T2 : TrC, r : T2.ops & Rd | let x = r.obj, wi=r.sees | 
    {
        wi.tr = T1
        some wj : (T1.ops - wi) & Wr | {
            wj.obj = x
            gt[wj, wi]
        }
    }
}

assert PL2 {
    // not G1a
    not G1b
}

//check PL1 
check PL2 

// run {}

/*
run {
    all t : Tr | some tr.t
    all obj : Obj | #obj.vers > 1

} for 3 but exactly 3 Tr, exactly 2 Obj, exactly 3 Version
*/