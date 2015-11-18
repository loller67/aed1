aux primeros (l:[(T,S)]) : [T] = [prm(x)|x ← l];
aux segundos (l:[(T,S)]) : [S] = [sgd(x)|x ← l];
aux sinRepetidos (l:[T]) : Bool = (∀i,j ← [0..|l|),i 6= j)li6= lj;
aux vivos (ps: [Personaje]) : [Personaje] = [p|p ← ps,vida(p) > 0];
aux esPosicionValida (p: Personaje, j: Juego) : Bool = (0 <= prm(posicion(j,p)) <= prm(tablero(j))) ^ (0 <= sgd(posicion(j,p)) <= sgd(tablero(j)));
aux todasLasVictimas (ps:[Personaje]) : [String] = [v |p ← ps,v ← victimas(p)];
aux buscarPos (p: Personaje, pos: [(String, Posicion)]) : Posicion = [sgd(x)|x ← ps,prm(x) == nombre(p)0];
aux maxNivel (i:juego):Int = sum[nivelPersonaje(p)|p<- (i), todos([nivelPersonaje(p)>= nivelPersonaje(q) | q<- players(i)];
aux nivelPersonaje (p:Personaje) : Int = level(habilidades (p) [0])+level (habilidades(p)[1]);
aux nivelDeVenganza (p:Personaje,j: Juego) : Int = sum [ |Victimas(x)| x <- players(j), nombre(x) € victimas (p)];
aux dosMataAUno (i: Juego,r,s: Personaje): Bool= alguno([vidaActual(r)<= poder(h) ^ distancia( posicion (r), posicion (q))<= rango(h) | h<- habilidad(s), tipo(h) != sanar]);
aux esReVivo(a:Personaje,l:[Personaje]):Bool=(∀ p <- l) vidaActual(a) >= vidaActual (p);
aux casiMuerto(b:Personaje,l:[Personaje]):Bool=(∀ p <- vivos(l)) vidaActual(b) <= vidaActual (p);
aux quitoDos(a,b:T,l:[T]):[T]=[x | x <- l , x != a ^ x != b];
aux distancia(a:(Int, Int), b:(Int, Int)) : Int = |prm(a) - prm(b)| + |sgd(a) - sgd(b)|;
aux rangoMax(p: Personaje) : Int = max(rango(habilidades(p)[0]), rango(habilidades(p)[1]);

aux ataquesPosibles (j: Juego, p: Personaje) : [(Habilidad, Personaje)] = [(h,i)|h<-habilidades(p),i<- vivos (players(j)), distancia (posicion(j,i),posicion(j,p)) <= rango(h)]);

problema victimasPorCercania (j:Juego, p:Personaje) = result :[Personaje]{
requiere p € vivos (players(j));
asegura mismos(result,[i|i<- vivos (players(j)), distancia (posicion(j,i),posicion(j,p)) <= rangoMax(p)]); 
asegura todos([distancia (posicion(j,p), posicion(j,result[i]) <= distancia (posicion(j,p), posicion (j, result[i+1])) | i<-[0.. |res|-1)]) ;
}

problema posicionesSeguras (j:juego, p:Personaje)= result :[posicion]{
requiere p € vivos(players(j));
asegura mismos (result, [(x,y)| x,y <- [0.. |tablero(j)|), distancia ((x,y), posicion (j,p)) <= velocidad (p)) ^ todos ([distancia ((x,y), posicion(j,q)) >= rangomax(p) | q <- vivos(players(j)),q != p])]);
}

problema losMasPoderosos (j:Juego)=result: [Personaje]{
asegura mismos( result, [p|p<- players (j), nivelPersonaje(p)== maxnivel(j)]
}

problema elVengador (j:juego) =result:Personaje{
asegura todos([ nivelDeVenganza (result,j) >=nivelDeVenganza (p,j) | p<- players(j)]);
}

problema jaqueMate(j:Juego,p:Personaje)= result:Bool{
requiere p € vivos(players(j));
asegura result == alguno([ dosMataAUno(j,p,q) | q<- vivos(players(j)) , q !=p]);
}
 
problema teletransportacion (j: Juego){
requiere |vivos(players(j))| > 1 ;
modifica j;
asegura tablero(j) == tablero (pre(j));
asegura soloDosCambian: (existen p1, p2 <- players(pre(j)), esReVivo(p1) ^ casiMuerto(p2)) 
(existen q1, q2 <- players(j)) 
(nombre(p1) == nombre(q2) ^ nombre(p2) == nombre(q1)) ^
(mismos(habilidades(p1), habilidades(q2)) ^ mismos(habilidades(p2),habilidades(q1))) ^
(vidaMaxima(p1) == vidaMaxima(q2) ^ vidaMaxima(p2) == vidaMaxima(q1)) ^
(velocidad(p1) == velocidad(q2) ^ velocidad(p2) == velocidad(q1)) ^
(mismos(victimas(p1), victimas(q2)) ^ mismos(victimas(p2),victimas(q1))) ^
(esReVivo(q1) ^ casiMuerto(q2)) ^ 
(posicion(pre(j),p1) == posicion(j,q2) ^ posicion(pre(j),p2) == posicion(j,q1))
^       mismos(quitoDos(players(pre(j))),quitoDos(players(j)))
^       (∀ p <- players(pre(j)), p != p1 ^ p != p2) (posicion(j,p) == posicion(pre(j),p))
;
}

problema atacar (j: Juego, p: Personaje){
requiere estaVivo: vidaActual(p) > 0;
modifica j, p;
asegura tableroNoCambia: tablero(j) == tablero(pre(j));
asegura lePegaAUnoSolo: (∃q <- players(pre(j)), h <- habilidades(pre(p)), distancia(posicion(pre(j),q), posicion(pre(j),pre(p))) <= rango(h))
((∀ w <- players(pre(j)), w != q, w != p) (w € players(j)))^ (∃r <- players(j)) ((nombre(r) == nombre(q) ^ velocidad(r) == velocidad(q) ^ vidaMaxima(r) == vidaMaxima(q))
^ ifthenelse(q == pre(p), ifthenelse(TipoHabilidad(h) == Sanar, vidaActual(p) == min(vidaMaxima(p),vidaActual(pre(p)) + poder(h)) ^ habilidades(p) == habilidades(pre(p)) ^ victimas(p) == victimas(pre(p)), ifthenelse(poder(h) < vidaActual(pre(p)), vidaActual(p) == vidaActual(pre(p)) - poder(h) ^ habilidades(p) == habilidades(pre(p)) ^ victimas(p) == victimas(pre(p)), vidaActual(p) == 0 ^ mismos(victimas(pre(p)),[nombre(p)] ++ victimas(p)) ^ ((level(habilidades(p)[0]) == level(habilidades(pre(p))[0]) + 1 ^ level(habilidades(p)[1]) == level(habilidades(pre(p))[1])) v (level(habilidades(p)[0]) == level(habilidades(pre(p))[0]) ^ level(habilidades(p)[1]) == level(habilidades(pre(p))[1]) + 1)) ^ posicion(j,p) == (-1,-1))), ifthenelse(TipoHabilidad(h) == Sanar, vidaActual(r) == min(vidaMaxima(q),vidaActual(q) + poder(h)) ^ habilidades(p) == habilidades(pre(p)) ^ victimas(p) == victimas(pre(p)),ifthenelse(poder(h) < vidaActual(q), vidaActual(r) == vidaActual(q) - poder(h) ^ habilidades(p) == habilidades(pre(p)) ^ victimas(p) == victimas(pre(p)), vidaActual(r) == 0 ^ mismos(victimas(pre(p)),[nombre(q)] ++ victimas(p)) ^ ((level(habilidades(p)[0]) == level(habilidades(pre(p))[0]) + 1 ^ level(habilidades(p)[1]) == level(habilidades(pre(p))[1])) v (level(habilidades(p)[0]) == level(habilidades(pre(p))[0]) ^ level(habilidades(p)[1]) == level(habilidades(pre(p))[1]) + 1)))) ^ habilidades(r) == habilidades(q) ^ victimas(r) == victimas(q));
}