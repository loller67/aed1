package tpalgo1;

import java.awt.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.io.IOException;
import java.io.Writer;
import java.util.StringTokenizer;

public class Juego 
{
	private Tablero tablero;
	private ArrayList<Personaje> personajes;
	private Map<String, Posicion> posiciones;
	
	public Juego(ArrayList<Personaje> p, Map<String, Posicion> pos, Tablero t) {
		this.tablero = t;
		this.personajes = p;
		this.posiciones = pos;
	}
	
	public Tablero getTablero() {
		return tablero;
	}

	public ArrayList<Personaje> getPersonajes() {
		return personajes;
	}
	
	public Posicion posicion(Personaje p)
	{
		return this.posiciones.get(p);
	}
	
	public boolean jaqueMate(Personaje p)
	{
		int n = 0;
		while (n<this.getPersonajes().size())
		{
			Personaje per = this.getPersonajes().get(n) ;
			int h = 0;
			if (per.getVidaActual() > 0){
				while(h<=1)
				{
					Habilidad habil =	per.getHabilidades().get(h);	
					if ( habil.getTipo()!= TipoHabilidad.Sanar ^ habil.getPoder() >= p.getVidaActual() ^ habil.getRango()>= distancia(this.posicion(p),this.posicion(per)) ) {return true;}
					h++;
				}
			}
			n++;
		}
		return false;
	}
	
	public ArrayList<Personaje> victimasPorCercania(Personaje p)
	{
		int contador = 0;
		ArrayList<Personaje> per = new ArrayList<Personaje>();
		
		while(contador < this.getPersonajes().size())
		{
			if (this.getPersonajes().get(contador).getVidaActual() > 0){
				
				if (distancia(this.posicion(this.getPersonajes().get(contador)),this.posicion(p)) <= rangomax(p))
				{
					per.add(this.getPersonajes().get(contador));
				}
			}
			contador++;
		}
		contador=0;
		int i=0;
		boolean ord = true;
		while (ord)
		{
			ord = false;
			i++;
			contador=0;
			while (contador < per.size()-i)
			{
				if (distancia(this.posicion(per.get(contador)),this.posicion(p))> distancia(this.posicion(per.get(contador+1)),this.posicion(p)))
				{
					Personaje sust = per.get(contador);
					per.set(contador, per.get(contador+1));
					per.set(contador+1,sust);
					ord=true;
				}
				contador++;
			}
		}
		return per;
	}
	
	public ArrayList<Posicion> posicionesSeguras(Personaje p)
	{
		int i = 0;
		int j = 0;
		ArrayList <Posicion> lista = new ArrayList <Posicion> ();
		
		while (i < this.getTablero().getAncho())
		{
			while(j< this.getTablero().getAlto())
			{
				Posicion pos = new Posicion (i,j);
				if(distancia(pos,this.posicion(p)) <= p.getVelocidad())
				{
				lista.add(pos);
				}
			j++;	
			}
		j=0;
		i++;
		}
		i = 0;
		
		while(j<lista.size())
		{
			while (i<this.getPersonajes().size())
			{
				if (this.getPersonajes().get(i).getVidaActual() > 0){
					
					if (distancia(this.posicion(this.getPersonajes().get(i)),lista.get(j))<= rangomax(this.getPersonajes().get(i)) && this.getPersonajes().get(i) != p)
					{
						lista.remove(j);
						j--;
						i = this.getPersonajes().size();
					}
				}
			i++;	
			}
		i=0;
		j++;
		}
	return lista;
	}
	
	public ArrayList<Personaje> losMasPoderosos()
	{
		int i = 0;
		ArrayList<Personaje> lista = new ArrayList<Personaje>();
		
		while (i < this.getPersonajes().size())
		{
			if ( nivelhabilidades (this.getPersonajes().get(i)) == maxlevel(this))
			{
				lista.add(this.getPersonajes().get(i));
			}
			i++;
		}
		return lista;
	}
	
	public Personaje elVengador()
	{
		int i = 0;
		int vengador = 0;
		int indice = 0;
		
		while (i < this.getPersonajes().size())
		{
			if (niveldevenganza(this.getPersonajes().get(i),this) > vengador)
			{
				vengador = niveldevenganza(this.getPersonajes().get(i),this);
				indice = i;
			}
			i++;
		}
		return this.getPersonajes().get(indice);
	}
	
	public void teletransportacion()
	{
		Personaje p =  pdemayorvida(this);
		Personaje q =  pdemenorvida(this);
		int vida = 0;
		
		
		
		Posicion x = this.posicion(p);
		
		this.posicion(p).setX(this.posicion(q).getX());
		this.posicion(p).setY(this.posicion(q).getY());
		
		this.posicion(q).setX(x.getX());
		this.posicion(q).setY(x.getY());
		
		if (p.getVidaActual() >= q.getVidaMaxima()){vida = q.getVidaMaxima();}
		else{vida = p.getVidaActual();}
		
		p.setVidaActual(q.getVidaActual());
		q.setVidaActual(vida);
	}
	
	public void atacar(Personaje p)
	{

		int h = 0;
		int i = 0;
		boolean ataque = false;
		ArrayList<Personaje> victimus = victimasPorCercania(p);
		if ((jaqueMate(p) ^ (p.getHabilidades().get(0).getTipo() == TipoHabilidad.Sanar||p.getHabilidades().get(1).getTipo() == TipoHabilidad.Sanar) ) || victimus.size() == 0)
		{
			while (h < 2)
			{
				if(p.getHabilidades().get(h).getTipo() == TipoHabilidad.Sanar)
				{
					if(p.getHabilidades().get(h).getPoder() + p.getVidaActual() >= p.getVidaMaxima())
					{
						p.setVidaActual(p.getVidaMaxima());
						
					}
					else
					{
						p.setVidaActual(p.getVidaActual() + p.getHabilidades().get(h).getPoder());
					}
				ataque = true;
				}
			h++;
			}
			if (ataque == false)
			{
				ataque = true;
			}

		}
		else
		{
			while (i < victimus.size() ^ ataque == false)
			{
				while (h < 2)
				{
					if(p.getHabilidades().get(h).getTipo() != TipoHabilidad.Sanar ^ p.getHabilidades().get(h).getPoder() >= victimus.get(i).getVidaActual() ^ ataque == false)
					{
						victimus.get(i).setVidaActual(0);
						p.agregarVictima(victimus.get(i).getNombre());
						this.posiciones.remove(victimus.get(i));
						ataque = true;
						if(p.getHabilidades().get(1-h).getTipo() == TipoHabilidad.Sanar)
						{
							if (p.getHabilidades().get(1-h).getPoder() < p.getVidaMaxima())
							{
								p.getHabilidades().get(1-h).setLevel(p.getHabilidades().get(1-h).getLevel() + 1);
							}
							else
							{
								p.getHabilidades().get(h).setLevel(p.getHabilidades().get(h).getLevel() + 1);
							}
						}
						else
						{
							if (p.getHabilidades().get(h).getTipo() != TipoHabilidad.ChuckNorris ^ p.getHabilidades().get(h).getPoder() < 30)
							{
								p.getHabilidades().get(h).setLevel(p.getHabilidades().get(h).getLevel() + 1);
							}
							else
							{
								if (p.getHabilidades().get(1-h).getTipo() != TipoHabilidad.ChuckNorris ^ p.getHabilidades().get(1-h).getPoder() < 30)
								{
									p.getHabilidades().get(1-h).setLevel(p.getHabilidades().get(1-h).getLevel() + 1);
								}
								else
								{
									if (p.getHabilidades().get(h).getTipo() == TipoHabilidad.ChuckNorris ^ p.getHabilidades().get(h).getPoder() < 30)
									{
										p.getHabilidades().get(h).setLevel(p.getHabilidades().get(h).getLevel() + 1);
									}
									else
									{
										p.getHabilidades().get(1-h).setLevel(p.getHabilidades().get(1-h).getLevel() + 1);
									}
								}
							}
							
						}
					}
					h++;
				}
				i++;
			}
		}
		if (ataque==false ^ victimus.size() != 0)
		{
			h=0;
			while (h < 2)
			{
				if(p.getHabilidades().get(h).getTipo() != TipoHabilidad.Sanar )
				{
					victimus.get(i).setVidaActual(victimus.get(0).getVidaActual() - p.getHabilidades().get(h).getPoder());
					ataque=true;
				}
				h++;
			}
			i++;
		}
		
	}

    public static void Escribir(Writer out, Juego t) throws IOException
	{
    	Tablero.Escribir(out, t.getTablero());
    	out.write("[ ");
    	int i = 0;
    	int n =t.getPersonajes().size() ;
    	while (i<n)
    	{
    		if (t.getPersonajes().get(i).getVidaActual()>0)
    		{
    		out.write(t.getPersonajes().get(i).getNombre());
    		Posicion.Escribir(out, t.posicion(t.getPersonajes().get(i)));
    		if (i!=n-1){out.write(" , ");}
    		}
    		i++;
    	}
    	out.write(" ] [ ");
    	i=0;
    	n=t.getPersonajes().size();
    	while (i<n)
    	{
    		Personaje.Escribir(out, t.getPersonajes().get(i));
    		if (i!=n-1){out.write(" , ");}
    		i++;
    	}
    	out.write(" ]");
	}
	
	public static Juego Leer(StringTokenizer in) throws IOException
	{
		StringTokenizer aux = new StringTokenizer(in.nextToken(")"));
		Tablero T = Tablero.Leer(aux);
		in.nextToken("[");
		in.nextToken(" ");
		String t = in.nextToken("]");
		System.out.print(t);
		aux = new StringTokenizer(t);
		StringTokenizer resto = in;
		Map <String,Posicion> posiciones = new HashMap <String, Posicion> ();
		String texto= aux.nextToken("(") ;
		aux.nextToken();
		String pos = aux.nextToken(")") + ")" ;
		Posicion P = Posicion.Leer(new StringTokenizer(pos));
		posiciones.put(texto, P);
		int h = aux.countTokens();
		while (h != 1)
		{
			aux.nextToken(",");
			aux.nextToken(" ");
			texto= aux.nextToken("(") ;
			aux.nextToken();
			pos = aux.nextToken(")") + ")" ;
			P = Posicion.Leer(new StringTokenizer(pos));
			posiciones.put(texto, P);
			h = aux.countTokens();
		}
		in.nextToken("[");
		ArrayList <Personaje> personajes = new ArrayList <Personaje>();
		while (resto.countTokens() - 2 > 0)
		{
			resto.nextToken();
			String text = resto.nextToken("]") + " ] " + resto.nextToken("]") + " ]";
			System.out.print(text);
			personajes.add(Personaje.Leer(new StringTokenizer (text)));
		}
		Juego j = new Juego ( personajes , posiciones , T);
		return j;
    }
	
		
	
	private static int distancia (Posicion p1, Posicion p2)
	{
		return (Math.abs(p1.getX() - p2.getX() ) + Math.abs(p1.getY() - p2.getY() ));
	}
	
	private static int rangomax (Personaje p)
	{
		return (Math.max(p.getHabilidades().get(0).getRango(),p.getHabilidades().get(1).getRango()));
	}
	
	private int maxlevel (Juego j)
	{
		int i = 0;
		int max = 0;
		while (i < j.getPersonajes().size())
		{
			if (nivelhabilidades(j.getPersonajes().get(i)) > max)
			{
				max = nivelhabilidades(j.getPersonajes().get(i));
			}
		}
		return max;
	}
	
	private int nivelhabilidades (Personaje p)
	{
		return (p.getHabilidades().get(0).getLevel() + p.getHabilidades().get(1).getLevel() );
	}
	
	private int niveldevenganza (Personaje p, Juego j)
	{
		int i = 0;
		int a = 0;
		
		while (i < p.getVictimas().size())
		{
			int q = j.getPersonajes().indexOf(p.getVictimas().get(i));
			a = a + j.getPersonajes().get(q).getVictimas().size();
			i ++;
		}
		return a;
	}
	
	private Personaje pdemenorvida (Juego i)
	{
		int indice = 0;
		int min =  i.getPersonajes().get(indice).getVidaActual();
		Personaje p = i.getPersonajes().get(indice);
		while (indice < i.getPersonajes().size())
		{
			indice++;
			if (i.getPersonajes().get(indice).getVidaActual() < min ^ i.getPersonajes().get(indice).getVidaActual() > 0)
			{
				min = i.getPersonajes().get(indice).getVidaActual();
				p=i.getPersonajes().get(indice);
			}
		}
		return p;
	}
	
	private Personaje pdemayorvida (Juego i)
	{
		int indice = 0;
		int max =  i.getPersonajes().get(indice).getVidaActual();
		Personaje p = i.getPersonajes().get(indice);
		while (indice < i.getPersonajes().size())
		{
			indice++;
			if (i.getPersonajes().get(indice).getVidaActual() > max)
			{
				max = i.getPersonajes().get(indice).getVidaActual();
				p=i.getPersonajes().get(indice);
			}
		}
		return p;
	}
}
