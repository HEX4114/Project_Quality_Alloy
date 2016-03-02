module projet

open util/ordering[Time]
open util/integer

-- Signatures
abstract sig Coordonnees{
	x: Int, y: Int,
}

sig Noeud extends Coordonnees {}

one sig Entrepot extends Coordonnees{}

sig Receptacle extends Coordonnees{}

some sig Drone{
	coord: one Coordonnees
}

sig Time{}

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

pred Voisin[n,m: Coordonnees]{
	eq[distanceDeManhattan[n, m], 1]
}

pred Superpose[n1, n2: Coordonnees]{
	n1 != n2 && eq[distanceDeManhattan[n1, n2], 0]
}

pred ObjetSurCoord [o, c: Coordonnees]{
	eq[o.x,c.x] && eq[o.y,c.y]
}

pred DroneUniqueEndroit[d1, d2 : Drone]
{
	d1 != d2 && d1.coord = d2.coord
}

pred DronesSimilaires[d1,d2 : Drone]{
	d1 = d2
}

/*pred init [t: Time] { -- on doit faire l'init pour un Time t
	-- tous les drones a l'entrepot
}

pred deplacerDrone [t, t': Time, c: Coordonnees] { -- ce qui se passe quand qqun entre dans la chambre
	d in c.drone.t -- drone a la coord c au Time t
	let cap = c.drone.cap |
		(cap = 0 and 
	let ck = r.currentKey | -- currentKey de la room
		(k = ck.t and ck.t' = ck.t) or -- le guest est le meme qu'avant, on change pas la k de la room
		(k = nextKey[ck.t, r.keys] and ck.t' = k) -- le gust change et la ck de la room prend la valeur de la k de la carte (qui est le next du set de key de la lock) 
	noRoomChangeExcept [t, t', r] -- ce qui ne doit pas changer
	noGuestChangeExcept [t, t', none]
	noFrontDeskChange [t, t']
	}*/


-- Invariants
fact {all n: Coordonnees| n.x >=0 && n.x <= 7 && n.y >= 0 && n.y <= 7}
fact EntrepotNonIsole {all e: Entrepot | some r: Receptacle | Atteignable[e, r]}
fact EntrepotDisjoint{one e: Entrepot | all r: Receptacle | ! eq[distanceDeManhattan[e ,r], 0]}
fact EcartReceptacles {all r: Receptacle | some r2: Receptacle | Atteignable[r,r2] &&r!=r2}
fact NoeudsDisjoints{all n1: Coordonnees| no n2: Coordonnees | Superpose[n1, n2]}
fact RNBsupZero {some c: Coordonnees | one r: Receptacle | ObjetSurCoord[r,c]}
fact EntrepotOrigine {one c: Coordonnees | one e: Entrepot | ( ObjetSurCoord[e,c] && eq[e.x,0] && eq[e.y,0])}
fact ReceptacleVoisinEntrepot {all e: Entrepot | some r: Receptacle| Voisin[e,r]}
fact DroneLocationUnique {all d1 : Drone| no d2 : Drone| DroneUniqueEndroit[d1,d2]}

/*fact{
	init [first] -- init pour le premier time de l'ordering Time
}*/

-- Assertions
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
-- false
assert CoordonneesPlusiersReceptacles {all c: Coordonnees | some r: Receptacle | ObjetSurCoord [r,c]}
--check CoordonneesPlusiersReceptacles
-- FAUX :assert DNBsupZero{some c: Coordonnees| one d: Drone | DronesSimilaires[c.drone, d] }
--check DNBsupZero
assert DronePosittion {}

pred go {}
run go for 10 but exactly 10 Drone, exactly 2 Time, 5 Int


