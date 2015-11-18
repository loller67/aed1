package backend;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.Writer;
import java.util.StringTokenizer;

public class FileHelp 
{
	public static <T> void Write(String filename, T w)
            throws FileNotFoundException, IOException {
		
		File aFile = new File(filename);
		
		Writer output = (new FileWriter(aFile));
		try 
		{
			if(w.getClass() == Posicion.class)
			{
				Posicion.Escribir(output, (Posicion) w);
			}
			if(w.getClass() == Tablero.class)
			{
				Tablero.Escribir(output, (Tablero) w);
			}
			if(w.getClass() == Personaje.class)
			{
				Personaje.Escribir(output, (Personaje) w);
			}
            if(w.getClass() == Habilidad.class)
            {
                Habilidad.Escribir(output, (Habilidad) w);
            }
            if(w.getClass() == Juego.class)
            {
                Juego.Escribir(output, (Juego) w);
            }
		}
		finally {
			output.close();
		}
	}
	
	public static <T> T Read(String filename, Class<T> t)
            throws FileNotFoundException, IOException {
		
		File aFile = new File(filename);
		InputStream input = new FileInputStream(aFile);
		
		StringTokenizer in = new StringTokenizer(readStream(input));
		
		T r = null;
		try {
			if(t == Posicion.class)
			{
				r = (T)Posicion.Leer(in);
			}
			if(t == Tablero.class)
			{
				r = (T)Tablero.Leer(in);
			}
			if(t == Personaje.class)
			{
				r = (T)Personaje.Leer(in);
			}
            if(t == (T)Habilidad.class)
            {
                r = (T)Habilidad.Leer(in);
            }
            if(t == (T)Juego.class)
            {
                r = (T)Juego.Leer(in);
            }
		}
		finally {
			input.close();
		}
		
		return r;
	}
	
	public static String readStream(InputStream is) {
	    StringBuilder sb = new StringBuilder();
	    try {
	        Reader r = new InputStreamReader(is);
	        int c = 0;
	        while ((c = r.read()) != -1) {
	            sb.append((char) c);
	        }
	    } catch (IOException e) {
	        throw new RuntimeException(e);
	    }
	    return sb.toString();
	}
}
