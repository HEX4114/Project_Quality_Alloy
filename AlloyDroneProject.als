module projet

open util/integer

-- Signatures
sig Coordonnees{
	x: Int, y: Int
}

abstract sig Noeud{
	coord: Coordonnees
}

one sig Entrepot extends Noeud{ -- Entrepot est un singleton

}

sig Receptacle extends Noeud{

}

sig Drone{
	node: Noeud
}

-- Fonctions Utilitaires
fun abs[n: Int] : Int {n<0 => (negate[n]) else (n) }

fun distanceDeManhattan[n,m: Noeud] : Int{
	add[abs[sub[m.coord.x,n.coord.x]], abs[sub[m.coord.y,n.coord.y]]]
}

-- Predicats
pred EstACoteDe[n,m: Noeud] { 
	eq[distanceDeManhattan[n, m], 1] -- distance de manhattan entre les n et m = 1
}

pred Atteignable[n, m: Noeud] {
	lte[distanceDeManhattan[n, m], 3]
}

pred Superpose[r1, r2: Receptacle]{
	r1 != r2 && eq[distanceDeManhattan[r1, r2], 0]
}

pred neq [n1, n2: Int] { int[n1] != int[n2] }

pred DronesNonSuperposes[d1,d2:Drone]{
	neq[d1.node.coord.x, d2.node.coord.x]
	neq[d1.node.coord.y, d2.node.coord.y]
}

-- Invariants
fact EntrepotNonIsole {one e: Entrepot | some r: Receptacle | EstACoteDe[e, r]}
fact EntrepotDisjoint{one e: Entrepot | all r: Receptacle | e.coord != r.coord}
fact EcartReceptacles {all r: Receptacle | some r2: Receptacle | Atteignable[r,r2]}
fact ReceptaclesDisjoints{all r1: Receptacle | no r2: Receptacle | Superpose[r1, r2]}
fact Drone {all d: Drone | some d2: Drone | DronesNonSuperposes[d,d2]}

pred go {}
run go

-- Assertions
assert ReceptaclesAtteignable {}


