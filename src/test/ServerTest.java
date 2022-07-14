package test;


import multiplayer.Client.ClientClasses.Client;
import multiplayer.Server.Server;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.BufferedReader;
import java.io.PrintWriter;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class ServerTest {

    Server server;

    @BeforeEach
    public void setUp() {
        server = new Server();
        server.startTest(6969);
    }


    @Test

    public void testInvalidUsernameHandling() {
        //The first 2 clients have invalid users (like "" or "~~~") which the server will
        //not accept, therefore the logged in client map size should only be 1 instead of 3.
        Client clientHuman = new Client();
        clientHuman.setUsername("");
        clientHuman.connect("localhost", 6969);

        Client clientHuman2 = new Client();
        clientHuman.setUsername("~~~~~~~");
        clientHuman.connect("localhost", 6969);

        Client clientHuman3 = new Client();
        clientHuman3.setUsername("test1");
        clientHuman.connect("localhost", 6969);

        assertEquals(1, server.getClientMap().size());
        server.stop();
    }

    @Test

    public void testInvalidCommandsHandling() {

        //Connect a client to the server
        Client clientHuman = new Client();
        clientHuman.setUsername("tester");
        clientHuman.connect("localhost", 6969);

        //Get the reader/writers
        BufferedReader in = clientHuman.getIn();
        PrintWriter out = clientHuman.getOut();

        //Send a random input to the server
        out.println("adssadsdds");
        out.flush();

        //Impersonate a foreign log-in using invalid inputs
        out.println("HELLO~GOSICA");
        out.println("LOGIN~GOSICA");

        //If the server ignores these inputs, then the server should be alive and
        //the clientMap size should be 1, (not including the false login of course).
        assertTrue(server.isAlive());
        assertEquals(1, server.getClientMap().size());
        server.stop();
    }


}
