public class SglrJNI {
   static {
      System.loadLibrary("SglrJNI"); // hello.dll (Windows) or libhello.so (Unixes)
      init();
   }
   // A native method that receives nothing and returns void
   private static native void init();
   private static native byte[] parse(String parseTablePath, 
		   String input,
		   String startSymbol,
		   String inputFileName);

   public static void main(String[] args) {
	   System.out.println("Starting Java...");
		 byte[] result = SglrJNI.parse("Test.tbl", "1,2,3", "Exp","example.krule");
		 for (int i=0; i< result.length; i++) {
				System.out.print(result[i]);
				System.out.print(",");
     }
		 System.out.println();
   }
}
