package tpalgo1;

import java.io.IOException;
import java.io.Writer;
import java.util.StringTokenizer;

public class Posicion 
{
	public Posicion(int ax, int ay)
	{
		x=ax;
		y=ay;
	}
	
	public int getX() {
		return x;
	}
	public void setX(int x) {
		this.x = x;
	}

	public int getY() {
		return y;
	}

	public void setY(int y) {
		this.y = y;
	}

	private int x;
	private int y;
    
    public static void Escribir(Writer out, Posicion t) throws IOException
	{
    	out.write("( " + t.getX() + " , " + t.getY() + " )");
	}
	
	public static Posicion Leer(StringTokenizer in) throws IOException
	{
		in.nextToken();
		int x = Integer.valueOf(in.nextToken());
		in.nextToken();
		int y = Integer.valueOf(in.nextToken());
		Posicion pos = new Posicion (x,y);
		return pos;
    }
}
