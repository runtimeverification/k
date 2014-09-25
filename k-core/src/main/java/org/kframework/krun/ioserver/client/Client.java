// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.ioserver.client;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;

public class Client {

    public static void main(String[] args) {

        try {
            InetAddress host = InetAddress.getLocalHost();
            Socket socket;

//            int i = 0;
            while (true) {
                try {
//                    System.out.println("Try " + i); i++;
                    socket = new Socket(host.getHostName(), 10000);
                    OutputStreamWriter osw = new OutputStreamWriter(
                            socket.getOutputStream());
                    osw.write("0\001writebyte\0011\00113\001\n");
                    osw.flush();
                    osw.close();
                    break;
                } catch (IOException e) {
                }
            }

        } catch (UnknownHostException e) {
            e.printStackTrace();
        }
    }
}
