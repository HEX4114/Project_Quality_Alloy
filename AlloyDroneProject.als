module projet

open util/integer

-- Signatures
sig Coordonnees{
	x: Int, y: Int
}

sig Noeud{
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
/*pred EstACoteDe[n,m: Noeud] { 
	eq[distanceDeManhattan[n, m], 1] -- distance de manhattan entre les n et m = 1
}*/

pred Atteignable[n, m: Noeud] {
	lte[distanceDeManhattan[n, m], 3]
}

pred nonAtteignable[n, m: Noeud] {
	gt[distanceDeManhattan[n, m], 3]
}

pred Superpose[n1, n2: Noeud]{
	n1 != n2 && eq[distanceDeManhattan[n1, n2], 0]
}


pred DronesSuperposes[d1,d2:Drone]{
	d1 != d2 && eq[distanceDeManhattan[d1.node, d2.node], 0]
}

-- Invariants
fact {all n: Noeud | n.coord.x >=0 && n.coord.x <= 7 && n.coord.y >= 0 && n.coord.y <= 7}
fact EntrepotNonIsole {all e: Entrepot | some r: Receptacle | Atteignable[e, r]}
fact EcartReceptacles {all r: Receptacle | some r2: Receptacle | Atteignable[r,r2] && r != r2}
fact NoeudsDisjoints{all n1: Noeud | no n2: Noeud | Superpose[n1, n2]}
fact Drone {all d: Drone | no d2: Drone | DronesSuperposes[d,d2]}

-- Assertions
assert DistanceManthattanPositive{all n1: Noeud | no n2: Noeud | distanceDeManhattan[n1, n2]<0}
--check DistanceManthattanPositive for 5 but 5 Int expect 0
assert ReceptaclesAtteignables {all r: Receptacle | no r2: Receptacle | nonAtteignable[r,r2]}
--check ReceptaclesAtteignables

pred go {}
run go


