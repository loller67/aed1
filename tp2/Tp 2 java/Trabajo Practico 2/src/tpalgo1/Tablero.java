package tpalgo1;

import java.io.IOException;
import java.io.Writer;
import java.util.StringTokenizer;

public class Tablero 
{
	
	public Tablero(int an, int al)
	{
		ancho = an;
		alto = al;
	}
	
	private int ancho;
	private int alto;
	
	public int getAncho() {
		return ancho;
	}
	
	public int getAlto() {
		return alto;
	}
	
	public static void Escribir(Writer out, Tablero t) throws IOException
	{
		out.write("( " + t.getAncho() + " , " + t.getAlto() + " )");
	}
	
	public static Tablero Leer(StringTokenizer in) throws IOException
	{
		int x = Integer.valueOf(in.nextToken());
		in.nextToken();
		int y = Integer.valueOf(in.nextToken());
		Tablero t = new Tablero (x,y);
		return t;
    }
	

}
