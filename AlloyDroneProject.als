module projet

open util/integer

-- Signatures
sig Coordonnees{
	x: Int, y: Int
}

sig Noeud extends Coordonnees {
	drone : lone Drone,
	receptacle: lone Receptacle
}

one sig Entrepot extends Coordonnees{ -- Entrepot est un singleton
	drone : some Drone -- garantie que DNB sup zero
}

sig Receptacle extends Coordonnees{
	drone : lone Drone
}

some sig Drone{
}

-- Fonctions Utilitaires
fun abs[n: Int] : Int {n<0 => (negate[n]) else (n) }

fun distanceDeManhattan[n,m: Coordonnees] : Int{
	add[abs[sub[m.x,n.x]], abs[sub[m.y,n.y]]]
}

-- Predicats
/*pred EstACoteDe[n,m: Noeud] { 
	eq[distanceDeManhattan[n, m], 1] -- distance de manhattan entre les n et m = 1
}*/

pred Atteignable[n, m: Coordonnees] {
	lte[distanceDeManhattan[n, m], 3]
}

pred nonAtteignable[n, m: Coordonnees] {
	gt[distanceDeManhattan[n, m], 3]
}

pred Superpose[n1, n2: Coordonnees]{
	n1 != n2 && eq[distanceDeManhattan[n1, n2], 0]
}

pred ObjetSurCoord [o, c: Coordonnees]{
	eq[o.x,c.x] && eq[o.y,c.y]
}


-- Invariants
fact {all n: Coordonnees| n.x >=0 && n.x <= 7 && n.y >= 0 && n.y <= 7}
fact EntrepotNonIsole {all e: Entrepot | some r: Receptacle | Atteignable[e, r]}
fact EntrepotDisjoint{one e: Entrepot | all r: Receptacle | (e.x != r.x && e.y != r.y)}
fact EcartReceptacles {all r: Receptacle | some r2: Receptacle | Atteignable[r,r2] &&r!=r2}
fact NoeudsDisjoints{all n1: Coordonnees| no n2: Coordonnees | Superpose[n1, n2]}
fact RNBsupZero {some c: Coordonnees | one r: Receptacle | ObjetSurCoord[r,c]}
fact EntrepotOrigine {one c: Coordonnees | one e: Entrepot | ( ObjetSurCoord[e,c] && eq[e.x,0] && eq[e.y,0])}


-- Assertions
assert DistanceManthattanPositive{all n1: Noeud | no n2: Noeud | distanceDeManhattan[n1, n2]<0}
--check DistanceManthattanPositive for 5 but 5 Int expect 0
assert ReceptaclesAtteignables {all r: Receptacle | no r2: Receptacle | nonAtteignable[r,r2]}
--check ReceptaclesAtteignables
assert EntrepotExist {one c: Coordonnees | one e: Entrepot | ObjetSurCoord [e,c]}
--check EntrepotExist
assert CoordonneeSansReceptacle {some c: Coordonnees | no r: Receptacle | ObjetSurCoord[r,c]}
--check CoordonneeSansReceptacle
assert CoordonneesAvecReceptacle {some c: Coordonnees | one r: Receptacle | ObjetSurCoord [r,c]}
--check CoordonneesAvecReceptacle

pred go {}
run go 


