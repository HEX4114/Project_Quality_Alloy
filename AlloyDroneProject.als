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

pred init [t: Time, d: Drone, e: Entrepot] { 	--On doit faire l'init pour un Time t
	d.coord.t = e && 	d.batterie.t = 3 			--Tous les drones a l'entrepot et chargés
}

pred ActionDrone [t, t': Time, d: Drone] {
	some r:Receptacle | all e:Entrepot |
	((d.batterie.t < 3 && (d.coord.t in r || d.coord.t in e))
	implies (
		--Recharger[t, t', d]
		RechargerBatterie[t, t', d, d.coord.t]
	)else (
		--Attendre[t, t', d]
		Deplacer [t, t', d]
	))
}

pred Deplacer [t, t': Time, d: Drone]{
	let IndActuellesCoord = d.cmd.chemin.idxOf[d.coord.t] |
		d.coord.t =  d.cmd.chemin[IndActuellesCoord] &&
		d.coord.t' = d.cmd.chemin[add[IndActuellesCoord,1]] &&
		d.batterie.t' = sub[d.batterie.t, 1]

}

pred InstancierChemin [s: seq Coordonnees]{
	let n = s.inds |
	all x: Int & n |
	Voisin[s[x], s[add[x,1]]]
}

pred Attendre [t, t' :Time, d:Drone]{
	d.coord.t' = d.coord.t &&
	d.batterie.t' = d.batterie.t
}

pred Recharger [t, t' :Time, d:Drone]{
	d.coord.t' = d.coord.t &&
	d.batterie.t' = add[d.batterie.t, 1]
}

pred RechargerBatterie [t, t': Time, d: Drone, c: Coordonnees]{ 																--Si le drône est à l'entrepôt ou sur un receptacle et que sa batterie 
	d.coord.t = c and d.batterie.t<3 and d.coord.t' = d.coord.t and d.batterie.t' = add[d.batterie.t,1] 	--n'est pas pleine alors il y reste jusqu'à la charge complète

}

-----Invariants-----
--Limites coordonnées
fact {all n: Coordonnees| n.x >=0 && n.x <= 7 && n.y >= 0 && n.y <= 7}
--Entrepôt
fact EntrepotNonIsole {all e: Entrepot | some r: Receptacle | Atteignable[e, r]}
fact EntrepotDisjoint{one e: Entrepot | all r: Receptacle | ! eq[distanceDeManhattan[e ,r], 0]}
--Réceptacles et noeuds
fact EcartReceptacles {all r: Receptacle | some r2: Receptacle | Atteignable[r,r2] &&r!=r2}
fact NoeudsDisjoints{all n1: Coordonnees| no n2: Coordonnees | Superpose[n1, n2]}
fact UnDroneReceptacle {all d1:Drone | all r:Receptacle | all t:Time | no d2 : Drone | d1 != d2 && d1.coord.t = r && d2.coord.t = r }
fact UnDroneNoeud {all d1:Drone | all n:Noeud |all t:Time |no d2 : Drone |d1 != d2 && d1.coord.t = n && d2.coord.t = n }
--Poids
fact PoidSupZero{all c: Commande | gt[c.poid,0]}
fact PoidInfPoidMax{}
--Batteries
fact BatterieMaxMin{all d: Drone | all t:Time | d.batterie.t>=0 && d.batterie.t<=3}
fact BatterieVide{all d: Drone | some r: Receptacle | some e: Entrepot | all t: Time | (d.batterie.t = 0 && (d.coord.t = r || d.coord.t = e)) || (d.batterie.t > 0)} --Si batterie = 0 alors le drône doit être sur "r" ou "e"
--Livraisons

fact LivraisonDerniereCoord {all c: Commande | all e: c.chemin.elems | c.chemin.last = c.destination && c.chemin.idxOf[e] = c.chemin.lastIdxOf[e]}
fact LivraisonPremiereCoord {all c: Commande | all e: Entrepot | c.chemin.first = e}
fact LivraisonEcartCoord {all c: Commande | InstancierChemin[c.chemin]}
fact LivraisonUnMinimumLoinQuandMemeASupprimer{all d: Drone | all e:Entrepot | gt[distanceDeManhattan[e, d.cmd.destination], 2]}
--Start
fact start{

	all d: Drone | all e: Entrepot | init [first, d, e] -- init pour le premier time de l'ordering Time
	all t: Time-last | let t' = t.next | -- pour tous les Time t on definit le Time suivant t'
		all d: Drone |
			ActionDrone [t, t', d]

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
assert accesDestination{all d:Drone | one t: Time | d.cmd.destination = d.coord.t} --Est ce qu'on va bien a la destination ?
--check accesDestination
assert UniciteEtapeLivraison{all d:Drone | !d.cmd.chemin.hasDups}
--check UniciteEtapeLivraison

--index de l'entrepot dans un chemin est bien 0
assert IndexEntrepotChemin{all d:Drone | all e:Entrepot | d.cmd.chemin.idxOf[e] = 0}
--check IndexEntrepotChemin
--Si batterie = 0, drone sur un receptacle ou un entrepot
assert BatterieNonNulle{all d:Drone | all r:Receptacle | all e:Entrepot | all t:Time | d.batterie.t =0 and (distanceDeManhattan[d.coord.t, r]=0 or distanceDeManhattan[d.coord.t, e]=0)}
--check BatterieNonNulle

-----RUN-----
pred go {}
--run go
//run go for 10 but exactly 13 Drone, 5 Int
run go for 8 but exactly 1 Drone, exactly 1 Commande, exactly 8 Time, exactly 3 Receptacle, 5 Int



