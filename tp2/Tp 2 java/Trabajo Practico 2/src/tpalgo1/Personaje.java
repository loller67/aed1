package tpalgo1;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.StringTokenizer;

public class Personaje 
{
	public Personaje(ArrayList<Habilidad> lasHabilidades, String elNombre, int laVida, int laVelocidad)
	{
		this.habilidades=lasHabilidades;
		this.nombre=elNombre;
		this.velocidad=laVelocidad;
		this.vidaActual=laVida;
		this.vidaMaxima=laVida;
		this.victimas= new ArrayList();
	}
		
	private String nombre;
	private ArrayList<Habilidad> habilidades;
	private int vidaMaxima;
	private int vidaActual;
	private int velocidad;
	private ArrayList<String> victimas;
	
	public String getNombre() {
		return nombre;
	}
	
	public ArrayList<Habilidad> getHabilidades() {
		return habilidades;
	}
	
	public int getVidaMaxima()
    {
		return vidaMaxima;
	}
	
	public int getVidaActual()
    {
		return vidaActual;
	}
	
	public void	setVidaActual(int vida)
    {
		if (vida <= this.vidaMaxima){this.vidaActual = vida;}
		else {this.vidaActual=this.vidaMaxima;}
	}

	public int getVelocidad()
    {
		return velocidad;
	}
	
	public ArrayList<String> getVictimas()
    {
		return victimas;
	}
	
	public void agregarVictima(String victima)
    {
		int i=0;
		boolean pertenece = false;
		while (i < this.victimas.size())
		{
			if (this.victimas.get(i)==victima){pertenece=true;}
			i++;
		}
		if (pertenece ==false){this.victimas.add(victima);}
	}
    
    public static void Escribir(Writer out, Personaje t) throws IOException
	{
    	out.write(t.getNombre() + " " + t.getVidaActual() + " " + t.getVidaMaxima() + " " + t.getVelocidad() );
    	out.write(" [ ");
    	Habilidad.Escribir(out, t.getHabilidades().get(0));
    	out.write(" , ");
    	Habilidad.Escribir(out, t.getHabilidades().get(1));
    	out.write(" ] [ ");
    	int i = 0;
    	int n = t.getVictimas().size();
    	while (i < n)
    	{
    		out.write(t.getVictimas().get(i));
    		if (i!=n-1){out.write(" , ");}
    		i++;
    	}
    	out.write(" ]");
	}
	
	public static Personaje Leer(StringTokenizer in) throws IOException
	{
		in.nextToken();
		String text =in.nextToken();
		String name = text;
		int vidaactual =Integer.valueOf(in.nextToken());
		int vidamax = Integer.valueOf(in.nextToken());
		int velocidad = Integer.valueOf(in.nextToken());
		in.nextToken();
		ArrayList <Habilidad> habilidades = new ArrayList <Habilidad> ();
		habilidades.add(Habilidad.Leer(new StringTokenizer(in.nextToken() + "  " + in.nextToken())));
		habilidades.add(Habilidad.Leer(new StringTokenizer(in.nextToken() + "  " + in.nextToken())));
		Personaje P = new Personaje (habilidades,name,vidamax,velocidad); 
		P.setVidaActual(vidaactual);
		in.nextToken("]");
		StringTokenizer aux = new StringTokenizer (in.nextToken("]") + "]");
		ArrayList <String> vict = new ArrayList <String>();
		while (aux.countTokens() - 2 > 0)
		{
			aux.nextToken();
			vict.add(aux.nextToken());
		}
		P.victimas.addAll(vict);
		return P;
    }
}