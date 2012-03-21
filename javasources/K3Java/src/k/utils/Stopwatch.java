package k.utils;

public class Stopwatch {
	private long start = 0;
	private long start2 = 0;

	public Stopwatch() {
		start = System.currentTimeMillis();
		start2 = start;
	}

	public void Start() {
		start = System.currentTimeMillis();
		start2 = start;
	}

	public void printIntermediate(String message) {
		long endd = System.currentTimeMillis();
		System.out.println(message + (endd - start2));
		start2 = endd;
	}

	public void printTotal(String message) {
		long endd = System.currentTimeMillis();
		System.out.println(message + (endd - start));
	}
}
