package client;

import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

public class Client {

	public static void main(String[] args) {

		try {
			InetAddress host = InetAddress.getLocalHost();
			Socket socket;

//			int i = 0;
			while (true) {
				try {
//					System.out.println("Try " + i); i++;
					socket = new Socket(host.getHostName(), 10000);
					OutputStreamWriter osw = new OutputStreamWriter(
							socket.getOutputStream());
					osw.write("0#writebyte#1#13#\n");
					osw.flush();
					osw.close();
					break;
				} catch (Exception e) {
				}
			}

		} catch (UnknownHostException e) {
			e.printStackTrace();
		}
	}
}
