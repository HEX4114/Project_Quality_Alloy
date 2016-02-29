module projet

open util/integer

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

fun abs[n: Int] : Int {n<0 => (negate[n]) else (n) }

fun distanceDeManhattan[n,m: Noeud] : Int{
	add[abs[sub[m.coord.x,n.coord.x]], abs[sub[m.coord.y,n.coord.y]]]
}

pred EstACoteDe[n,m: Noeud] { 
	eq[distanceDeManhattan[n, m], 1] -- distance de manhattan entre les n et m = 1
}

pred Atteignable[n, m: Noeud] {
	lte[distanceDeManhattan[n, m], 3]
}

pred neq [n1, n2: Int] { int[n1] != int[n2] }

pred DronesNonSuperposes[d1,d2:Drone]{
	neq[d1.node.coord.x, d2.node.coord.x]
	neq[d1.node.coord.y, d2.node.coord.y]
}


fact EntrepotNonIsole {one e: Entrepot | some r: Receptacle | EstACoteDe[e, r]}
fact EcartReceptacles {all r: Receptacle | some r2: Receptacle | Atteignable[r,r2]}
fact Drone {all d: Drone | some d2: Drone | DronesNonSuperposes[d,d2]}

pred go {}
run go

assert ReceptaclesAtteignable {}

/*sig Energie{
e: Int
}

--did (id drone), cid(id commande en cours), energie (energie en cours)
/*sig Drone{
did: Int, coord: Coordonnees, energie: Energie, DCAP: Int, cid: Int
}

sig Commande{
cid: Int, coord: Coordonnees, CAP: Int
}*/


