package ro.uaic.info.fmse.html;

public class Color{
	static public class RGB{
		private int r;
		private int g;
		private int b;
		
		public int getR() {
			return r;
		}

		public void setR(int r) {
			this.r = r;
		}

		public int getG() {
			return g;
		}

		public void setG(int g) {
			this.g = g;
		}

		public int getB() {
			return b;
		}

		public void setB(int b) {
			this.b = b;
		}
		
		public RGB(int _r,int _g, int _b){
			r = _r;
			g = _g;
			b = _b;
		}
		
		public String toString(){
			return "RGB : " + r + " " + g + " " + b;
		}
	}
	static public class HSL{
		private double h;
		private double s;
		private double l;
		
		public double getH() {
			return h;
		}

		public void setH(double h) {
			this.h = h;
		}

		public double getS() {
			return s;
		}

		public void setS(double s) {
			this.s = s;
		}

		public double getL() {
			return l;
		}

		public void setL(double l) {
			this.l = l;
		}

		public HSL(double _h, double _s, double _l){
			h = _h;
			s = _s;
			l = _l;
		}
		
		public String toString(){
			return "HSL" + h + " " + s + " " + l;
		}

	}
	
	static public HSL convertRGBtoHSL(RGB col){
		double var_R = ( col.getR() / 255.0 );                     //RGB from 0 to 255
		double var_G = ( col.getG() / 255.0 );
		double var_B = ( col.getB() / 255.0 );
		
		double var_Min = Math.min(Math.min( var_R, var_G), var_B );    //Min. value of RGB
		double var_Max = Math.max(Math.max( var_R, var_G), var_B );    //Max. value of RGB
		double del_Max = var_Max - var_Min;             //Delta RGB value
		
		double l = ( var_Max + var_Min ) / 2.0;
		double h = 0;
		double s = 0;
		double epsilon = 0.0001;
		
		if ( del_Max < epsilon )       // del_max == 0        //This is a gray, no chroma...
		{
			h = 0;                                //HSL results from 0 to 1
			s = 0;
		}
		else                                    //Chromatic data...
		{
			if ( l < 0.5 ) 
				s = del_Max / ( var_Max + var_Min );
			else           
				s = del_Max / ( 2 - var_Max - var_Min );
			
			double del_R = ( ( ( var_Max - var_R ) / 6 ) + ( del_Max / 2 ) ) / del_Max;
			double del_G = ( ( ( var_Max - var_G ) / 6 ) + ( del_Max / 2 ) ) / del_Max;
			double del_B = ( ( ( var_Max - var_B ) / 6 ) + ( del_Max / 2 ) ) / del_Max;
			
			if( var_R == var_Max ) 
				h = del_B - del_G;
			else if( var_G == var_Max )
				h = ( 1 / 3 ) + del_R - del_B;
			else if ( var_B == var_Max ) 
				h = ( 2 / 3 ) + del_G - del_R;
			
			 if ( h < 0 ) 
				   h += 1;
			 if ( h > 1 ) 
				   h -= 1;
		}
		return new Color.HSL(h,s,l);
	}
	
	static public RGB convertHSLtoRGB(HSL col){
		double r = 0, g = 0, b = 0;
		double l = col.getL();
		double s = col.getS();
		double h = col.getH();
		double epsilon = 0.0001;
		if (s < epsilon )                       //HSL from 0 to 1
		{
			r = l * 255;                     //RGB results from 0 to 255
			r = l * 255;
			r = l * 255;
		}
		else
		{
			double var_2, var_1;
			if ( l < 0.5 )
				var_2 = l * ( 1 + s );
			else
				var_2 = ( s + l ) - ( s * l );
			
			var_1 = 2 * l - var_2;
			
			r = 255 * Hue_2_RGB( var_1, var_2, h + ( 1.0 / 3 ) );
			g = 255 * Hue_2_RGB( var_1, var_2, h );
			b = 255 * Hue_2_RGB( var_1, var_2, h - ( 1.0 / 3 ) );
		}
				
		return new Color.RGB((int) r, (int) g, (int) b);
	}
	
	

	static private double Hue_2_RGB(double v1, double v2, double vH )             //Function Hue_2_RGB
	{
	   if ( vH < 0 ) 
		   vH += 1;
	   if ( vH > 1 ) 
		   vH -= 1;
	   
	   if ( ( 6 * vH ) < 1 ) 
		   return v1 + ( v2 - v1 ) * 6 * vH;
	   if ( ( 2 * vH ) < 1 ) 
		   return v2;
	   if ( ( 3 * vH ) < 2 ) 
		   return v1 + ( v2 - v1 ) * ( ( 2 / 3 ) - vH ) * 6;
		   
	   return v1;
	}
	
	
}
