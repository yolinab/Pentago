package multiplayer.Client;

import multiplayer.Client.ClientClasses.Client;
import multiplayer.Client.ClientClasses.ClientAI;
import multiplayer.Client.ClientClasses.ClientNaive;


import java.util.Scanner;

/**
 * Main class for manually creating a client to play on a Pentago server.
 */
public class ClientMain {

    private static String address = "localhost";
    private static int port = 6969;
    private static ClientInputParsing inputParsing;
    private static final Scanner sc = new Scanner(System.in);
    private static boolean clientChosen = false;

    /**
     * Chooses a client type according to the user's input.
     * @param input client type.
     */
    public static void chooseClientType(String input) {

        switch (input) {
            case "HUMAN":
                Client client = new Client();
                client.connect(address, port);
                inputParsing = new ClientInputParsing(client, sc);
                clientChosen = true;
                break;
            case "SMART":
                ClientAI clientAI = new ClientAI();
                clientAI.connect(address, port);
                inputParsing = new ClientInputParsing(clientAI, sc);
                clientChosen = true;
                break;
            case "NAIVE":
                ClientNaive clientNaive = new ClientNaive();
                clientNaive.connect(address, port);
                inputParsing = new ClientInputParsing(clientNaive, sc);
                clientChosen = true;
                break;
            default:
                System.err.println("Invalid client type. Please try again by choosing" +
                        " one of the clients.");
        }
    }

    public static void main(String[] args) {

        //TOM's server connection details

        //130.89.253.64
        //55555


        System.out.println("Please input a valid ip address. Press ENTER for localhost");
        String tempAddress = sc.nextLine();
        //I am aware that Apache has an ipv4 address checker, but I preferred not to use any
        //libraries for this project. Even if you introduce such an address, it will say that
        //it cannot connect to the host and close the client.
        if (tempAddress.length() > 50) {
            System.err.println("Invalid ip address.");
            System.exit(0);
        }
        address = tempAddress;
        System.out.println("Please input a valid port number.");
        try {
            port = Integer.parseInt(sc.nextLine());
        } catch (NumberFormatException e) {
            System.err.println("Invalid port range. (0 - 65535)");
            System.exit(0);
        }
        while (port < 0 || port > 65536) {
            System.out.println("Invalid port range. (0 - 65535)");
            port = Integer.parseInt(sc.nextLine());
        }


        while (!clientChosen) {
            System.out.println("Choose a client -> \"NAIVE\" , \"SMART\", \"HUMAN\"");
            String clientType = sc.nextLine().toUpperCase();
            chooseClientType(clientType);
        }
        while (true) {
            try {
                inputParsing.parseInput();
            } catch (ArrayIndexOutOfBoundsException e) {
                System.err.println("Invalid move! Please try again using the MOVE command.");
            }
        }
    }
}
