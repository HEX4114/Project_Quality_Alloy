module projet

open util/ordering[Time]
open util/integer

-----SIGNATURES-----
abstract sig Coordonnees{
	x: Int, y: Int,
}

sig Noeud extends Coordonnees {}

one sig Entrepot extends Coordonnees{}

some sig Receptacle extends Coordonnees{
	poidMax: Int	
}

some sig Drone{
	coord: Coordonnees one -> Time,
	batterie: Int one -> Time,
	poidMax : Int
}


some sig Commande{
	r: one Receptacle,
	produits: set Int
}

sig Time{}

-----FONCTIONS UTILITAIRES-----
fun abs[n: Int] : Int {n<0 => (negate[n]) else (n) }

fun distanceDeManhattan[n,m: Coordonnees] : Int{
	add[abs[sub[m.x,n.x]], abs[sub[m.y,n.y]]]
}

-----PREDICATS-----
pred Atteignable[n, m: Coordonnees] {
	lte[distanceDeManhattan[n, m], 3]
}

pred nonAtteignable[n, m: Coordonnees] {
	gt[distanceDeManhattan[n, m], 3]
}

pred Voisin[n,m: Coordonnees]{
	eq[distanceDeManhattan[n, m], 1]
}

pred Superpose[n1, n2: Coordonnees]{
	n1 != n2 && eq[distanceDeManhattan[n1, n2], 0]
}

pred ObjetSurCoord [o, c: Coordonnees]{
	eq[o.x,c.x] && eq[o.y,c.y]
}


pred DronesSimilaires[d1,d2 : Drone]{
	d1 = d2
}

pred init [t: Time, d: Drone, e: Entrepot] { -- on doit faire l'init pour un Time t
	d.coord.t = e -- tous les drones a l'entrepot
	d.batterie.t = 3
}

pred deplacerDrone [t, t': Time, d: Drone] {
	d.coord.t'.x = add[d.coord.t.x,1]&&
	d.batterie.t' = sub[d.batterie.t, 1]
}


-----Invariants-----
fact {all n: Coordonnees| n.x >=0 && n.x <= 7 && n.y >= 0 && n.y <= 7}
fact EntrepotNonIsole {all e: Entrepot | some r: Receptacle | Atteignable[e, r]}
fact EntrepotDisjoint{one e: Entrepot | all r: Receptacle | ! eq[distanceDeManhattan[e ,r], 0]}
fact EcartReceptacles {all r: Receptacle | some r2: Receptacle | Atteignable[r,r2] &&r!=r2}
fact NoeudsDisjoints{all n1: Coordonnees| no n2: Coordonnees | Superpose[n1, n2]}
fact EntrepotOrigine {one c: Coordonnees | one e: Entrepot | ( ObjetSurCoord[e,c] && eq[e.x,0] && eq[e.y,0])}
fact UnDroneReceptacle {all d1:Drone | all r:Receptacle | all t:Time | no d2 : Drone | d1 != d2 && d1.coord.t = r && d2.coord.t = r }
fact UnDroneNoeud {all d1:Drone | all n:Noeud |all t:Time |no d2 : Drone |d1 != d2 && d1.coord.t = n && d2.coord.t = n }
fact ReceptacleVoisinEntrepot {all e: Entrepot | some r: Receptacle| Voisin[e,r]}
fact PoidsSupZero{all c: Commande | all p:c.produits | gt[p,0]}
fact PoidMaxSupZero{all d: Drone| gt[d.poidMax,0]}
--fact PoidMaxReceptacleSupZero{all d: Drone| gt[d.poidMax,0]}
--fact PoidInfPoidMax{}

fact start{
	all d: Drone | all e: Entrepot | init [first, d, e] -- init pour le premier time de l'ordering Time
	all t: Time-last | let t' = t.next | -- pour tous les Time t on definit le Time suivant t'
		some d: Drone |
			deplacerDrone [t, t', d]
}

-----ASSERTIONS-----
assert DistanceManthattanPositive{all c1: Coordonnees | no c2: Coordonnees | distanceDeManhattan[c1, c2]<0}
--check DistanceManthattanPositive for 5 but 5 Int expect 0
assert ReceptaclesAtteignables {all r: Receptacle | no r2: Receptacle | nonAtteignable[r,r2]}
--check ReceptaclesAtteignables
assert EntrepotExist {one c: Coordonnees | one e: Entrepot | ObjetSurCoord [e,c]}
--check EntrepotExist
assert CoordonneeSansReceptacle {some c: Coordonnees | no r: Receptacle | ObjetSurCoord[r,c]}
--check CoordonneeSansReceptacle
assert CoordonneesAvecReceptacle {some c: Coordonnees | one r: Receptacle | ObjetSurCoord [r,c]&&!eq[c.x,0]&&!eq[c.y,0]}
--check CoordonneesAvecReceptacle
assert CoordonneesPlusiersReceptacles {all c: Coordonnees | some r: Receptacle | ObjetSurCoord [r,c]}
--check CoordonneesPlusiersReceptacles
assert ReceptacleNonOrigine {all e: Entrepot | no r: Receptacle | eq[distanceDeManhattan[e ,r], 0]}
--check ReceptacleNonOrigine
assert DroneEntrepotFirstR {all ddd: Drone | all rrr:Receptacle | ddd.coord.first != rrr}
--check DroneEntrepotFirstR
assert DroneEntrepotFirstN {all ddd: Drone | all nnn:Noeud | ddd.coord.first != nnn}
--check DroneEntrepotFirstN
assert ReceptaclesAtteignable{no r1: Receptacle | all r2: Receptacle | nonAtteignable[r1,r2]}
--check ReceptaclesAtteignable
assert ReceptacleUnDrone{all r:Receptacle | all t:Time|lone d:Drone| d.coord.t = r}
--check ReceptacleUnDrone
assert NoeudUnDrone{all n:Noeud | all t:Time|lone d:Drone| d.coord.t = n}
--check NoeudUnDrone
assert DronePosittion {}

-----RUN-----
pred go {}
//run go for 10 but exactly 13 Drone, 5 Int
run go for 5 but exactly 2 Drone, exactly 5 Time, 5 Int


