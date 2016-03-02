module projet

open util/ordering[Time] as to
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
	poidMax : Int,
	cmd : Commande
}

some sig Commande{
	destination: one Receptacle,
	poid: Int,
	chemin : seq Coordonnees
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
	d.coord.t = e && 	d.batterie.t = 3 -- tous les drones a l'entrepot et chargés
}

pred deplacerDrone [t, t': Time, d: Drone] {
	d.coord.t'.x = add[d.coord.t.x,1]&&
	d.batterie.t' = sub[d.batterie.t, 1]
}

pred InstancierChemin [s: seq Coordonnees]{
	let n = s.inds |
	all x: Int & n |
	Voisin[s[x], s[add[x,1]]]
}

-----Invariants-----
fact {all n: Coordonnees| n.x >=0 && n.x <= 7 && n.y >= 0 && n.y <= 7}
fact EntrepotNonIsole {all e: Entrepot | some r: Receptacle | Atteignable[e, r]}
fact EntrepotDisjoint{one e: Entrepot | all r: Receptacle | ! eq[distanceDeManhattan[e ,r], 0]}
fact EcartReceptacles {all r: Receptacle | some r2: Receptacle | Atteignable[r,r2] &&r!=r2}
fact NoeudsDisjoints{all n1: Coordonnees| no n2: Coordonnees | Superpose[n1, n2]}
fact UnDroneReceptacle {all d1:Drone | all r:Receptacle | all t:Time | no d2 : Drone | d1 != d2 && d1.coord.t = r && d2.coord.t = r }
fact UnDroneNoeud {all d1:Drone | all n:Noeud |all t:Time |no d2 : Drone |d1 != d2 && d1.coord.t = n && d2.coord.t = n }
fact PoidSupZero{all c: Commande | gt[c.poid,0]}
fact PoidInfPoidMax{}
fact BatterieMaxMin{all d: Drone | all t:Time | d.batterie.t>=0 && d.batterie.t<=3}
fact BatterieAugmenteE{all d: Drone | lone e: Entrepot | all t: Time-last | let t' = t.next | d.coord.t = d.coord.t' && d.coord.t = e && d.batterie.t' = add[d.batterie.t,1] && d.batterie.t<=3} --Attention au <= ou <, dépendra de la fonction déplacer.
fact BatterieAugmenteR{all d: Drone | lone r: Receptacle| all t: Time-last | let t' = t.next | d.coord.t = d.coord.t' && d.coord.t = r && d.batterie.t' = add[d.batterie.t,1] && d.batterie.t<=3}
fact BatterieFixeN{all d: Drone | lone n: Noeud | all t: Time-last | let t' = t.next | d.coord.t = d.coord.t' && d.coord.t = n && d.batterie.t' = d.batterie.t}


fact LivraisonDerniereCoord {all c: Commande | all e: c.chemin.elems | c.chemin.last = c.destination && c.chemin.idxOf[e] = c.chemin.lastIdxOf[e]}
fact LivraisonPremiereCoord {all c: Commande | all e: Entrepot | c.chemin.first = e}
fact LivraisonEcartCoord {all c: Commande | InstancierChemin[c.chemin]}

fact LivraisonUnMinimumLoinQuandMemeASupprimer{all d: Drone | all e:Entrepot | gt[distanceDeManhattan[e, d.cmd.destination], 2]}

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
assert CoordonneesPlusiersReceptacles {no c: Coordonnees | one r1: Receptacle | one r2: Receptacle | ObjetSurCoord [r1,c] && ObjetSurCoord[r2,c] && r1 != r2}
--check CoordonneesPlusiersReceptacles
assert RNBsupZero {some c: Coordonnees | one r: Receptacle | ObjetSurCoord [r,c]&&!eq[c.x,0]&&!eq[c.y,0]}
--check RNBsupZero
assert DNBsupZero{all t: Time | some c:Coordonnees | some d: Drone | eq[distanceDeManhattan[d.coord.t , c],0]}
--check DNBsupZero
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
assert UniciteEtapeLivraison{all d:Drone | !d.cmd.chemin.hasDups}
--check UniciteEtapeLivraison

--Est ce qu'on va bin a la destination ?
assert accesDestination{all d:Drone | one t: Time | d.cmd.destination = d.coord.t}
--check accesDestination


-----RUN-----
pred go {}
--run go
//run go for 10 but exactly 13 Drone, 5 Int
run go for 8 but exactly 1 Drone, exactly 1 Commande, exactly 3 Time, exactly 3 Receptacle, 5 Int



