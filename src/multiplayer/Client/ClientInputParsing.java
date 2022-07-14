package multiplayer.Client;

import ai.ComputerPlayer;
import ai.NaiveAI;
import ai.SmartAI;
import ai.SmartAIWithHints;
import game.Marble;
import multiplayer.Client.ClientClasses.Client;
import multiplayer.Client.ClientClasses.ClientAI;
import multiplayer.Client.ClientClasses.ClientNaive;
import multiplayer.Exceptions.IllegalMoveException;

import java.util.Scanner;

/**
 * Class that takes the input from the user and parses it according to the established protocol
 * of the Pentago server.
 *
 */
public class ClientInputParsing {
    private Client client;
    private final Scanner sc;
    private final SmartAIWithHints smartAIWithHints = new SmartAIWithHints(Marble.WHITE);
    private ClientAI clientAI;
    private ClientNaive clientNaive;
    private final SmartAI smartAI = new SmartAI(Marble.WHITE);
    private final NaiveAI naiveAI = new NaiveAI();


    //CONSTRUCTOR

    ClientInputParsing(Client client, Scanner sc) {
        this.client = client;
        this.sc = sc;
    }

    public ClientInputParsing(ClientAI clientAI, Scanner sc) {
        this.clientAI = clientAI;
        this.sc = sc;
    }

    public ClientInputParsing(ClientNaive clientNaive, Scanner sc) {
        this.clientNaive = clientNaive;
        this.sc = sc;
    }

////////////////////////////////////////////////////////////////////////////////////////////////////

    /**
     * Takes input from the user (system.in), parses it according to the protocol and then sends it
     * to the server.
     */


    protected void parseInput() {
        String input = sc.nextLine();
        switch (input.toUpperCase()) {
            case "LOGIN":
                if (client != null) {
                    client.login(input);
                } else if (clientNaive != null) {
                    clientNaive.login(input);
                } else if (clientAI != null) {
                    clientAI.login(input);
                }
                break;
            //LOGIN AND HELLO ARE NOT CURRENTLY IN USE BECAUSE THE
            // PROCESS IS AUTOMATED IN CLIENT MAIN!
            case "LIST":
                if (client != null) {
                    client.list();
                } else if (clientNaive != null) {
                    clientNaive.list();
                } else if (clientAI != null) {
                    clientAI.list();
                }
                break;
            case "QUEUE":
                if (client != null) {
                    client.queue();
                } else if (clientNaive != null) {
                    clientNaive.queue();
                } else if (clientAI != null) {
                    clientAI.queue();
                }
                break;
            case "MOVE":
                if (clientNaive != null || clientAI != null) {
                    System.err.println("Invalid command. Please type \"HELP\" for a list" +
                            " of possible commands.");
                    break;
                }
                try {
                    boolean clientInGame = client.isClientInGame();
                    if (clientInGame) {
                        System.out.println("Please input a move and rotation (ex. 1 1+ )");
                        input = sc.nextLine();
                        client.move(input);
                    } else {
                        System.err.println("You are in no game at the moment.");
                    }
                } catch (IllegalMoveException e) {
                    System.err.println(e.getMessage());
                }
                break;
            case "HINT":
                smartAiWithHintsMove();
                break;
            case "PING":
                if (client != null) {
                    client.ping();
                } else if (clientNaive != null) {
                    clientNaive.ping();
                } else if (clientAI != null) {
                    clientAI.ping();
                }
                break;
            case "PONG":
                if (client != null) {
                    client.pong();
                } else if (clientNaive != null) {
                    clientNaive.pong();
                } else if (clientAI != null) {
                    clientAI.pong();
                }
                break;
            case "QUIT":
                if (client != null) {
                    client.quit();
                } else if (clientNaive != null) {
                    clientNaive.quit();
                } else if (clientAI != null) {
                    clientAI.quit();
                }
                break;
            case "HELP":
                if (client != null) {
                    client.help();
                } else if (clientNaive != null) {
                    clientNaive.help();
                } else if (clientAI != null) {
                    clientAI.help();
                }
                break;
            default:
                System.err.println("Invalid command. Please type \"HELP\" for a list" +
                      " of possible commands.");
                break;
        }
    }

    /**
     * Parses the rotations given by our smartAI to rotations used by our human client.
     * @param rotation rotational index received from smartAI.
     * @return typical rotation String.
     */
    public String parseAIRotations(int rotation) {
        String parsedRotation = "";
        switch (rotation) {
            case 1:
                parsedRotation = "1+";
                break;
            case 2:
                parsedRotation = "1-";
                break;
            case 3:
                parsedRotation = "2+";
                break;
            case 4:
                parsedRotation = "2-";
                break;
            case 5:
                parsedRotation = "3+";
                break;
            case 6:
                parsedRotation = "3-";
                break;
            case 7:
                parsedRotation = "4+";
                break;
            case 8:
                parsedRotation = "4-";
                break;
        }
        return parsedRotation;
    }

    /**
     * Requests and makes a move and textual hints from the smartAI.
     */
    public void smartAiWithHintsMove() {
        int move = -1;
        if (client != null) {
            move = smartAIWithHints.determineMove(client.getBoard());
        }
        int rotation = smartAIWithHints.sendRotation();
        try {
            client.move(move + " " + parseAIRotations(rotation));
        } catch (IllegalMoveException e) {
            System.err.println(e.getMessage());
        }
    }

    /**
     * Makes a move using the smartAI.
     */
    public void smartAIMove() {
        int move = -1;

        if (clientAI != null) {
            move = smartAI.determineMove(clientAI.getBoard());
        }
        int rotation = smartAI.sendRotation();
        clientAI.move(move + " " + parseAIRotations(rotation));

    }

    /**
     * Makes a move using the NaiveAI.
     */
    public void naiveAiMove() {
        ComputerPlayer player = new ComputerPlayer(Marble.WHITE, naiveAI);
        int move = player.determineMove(clientNaive.getBoard());
        int rotation = naiveAI.determineAiRotation(clientNaive.getBoard());
        clientNaive.move(move + " " + parseAIRotations(rotation));
    }
}
