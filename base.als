/*

Source: Generalized Isolation Level Definitions,
Atul Adya, Barbara Liskov, Patrick O'Neil. 
Proceedings of the IEEE International Conference on Data Engineering, March 2000.

*/
open util/ordering[Version]

sig Tr {}

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
    tr : Tr
}

// all versioned values

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

check PL1 

/*
run {
    all t : Tr | some tr.t
    all obj : Obj | #obj.vers > 1

} for 3 but exactly 3 Tr, exactly 2 Obj, exactly 3 Version
*/