package multiplayer.Client.ClientClasses;

import game.Board;
import game.Marble;
import multiplayer.Client.ClientInputParsing;
import multiplayer.Parsers.RotationParsing;

import java.io.*;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Scanner;

/**
 * The Naive AI client for the Pentago Project.
 */
public class ClientNaive extends Client implements ClientInterface, Runnable {

    private Socket socket;
    private final Scanner sc = new Scanner(new InputStreamReader(System.in));
    private final ClientInputParsing clientInputParsing = new ClientInputParsing(this, sc);
    private BufferedReader in;
    private PrintWriter out;
    private final Board board = new Board();
    private final RotationParsing rotationParsing = new RotationParsing();
    private String username;
    private int move;
    private int x = 1;
    private boolean inGame = false;


    /**
     * Connects to a compatible server using the given ip/port combination.
     *
     * @param address ip address
     * @param port    port number
     */
    @Override
    public void connect(String address, int port) {
        try {
            socket = new Socket(address, port);
            in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
            out = new PrintWriter(socket.getOutputStream());
            Thread readerThread = new Thread(this);
            readerThread.start();

            if (username == null) {
                System.out.println("Input your username:");
                username = sc.nextLine();
            }

            hello("Gosica's magnificent NaiveClient");
            waitHalfASecond();
            login(username);

        } catch (UnknownHostException e) {
            System.err.println("Connection failed (the given host is unreachable).");
            close();
        } catch (IOException e) {
            System.err.println("The connection could not be established.");
            close();
        }
    }

    /**
     * Closes the connection to the server.
     */
    @Override
    public void close() {
        if (socket == null) {
            System.exit(0);
        }
        if (!socket.isClosed()) {
            try {
                socket.close();
                in.close();
                out.close();
            } catch (IOException e) {
                System.err.println("The connection could not be closed." +
                        " The program will terminate.");
            }
        }

    }

    /**
     * The initial message sent by the client once a connection has been established.
     *
     * @param input the initial message
     * @return true if message is sent successfully.
     */
    @Override
    public boolean hello(String input) {
        String filteredInput = input.replace("~", "");
        System.out.println("[CLIENT]" + "HELLO~" + filteredInput);
        out.println("HELLO~" + filteredInput);
        out.flush();
        return true;
    }

    /**
     * Sent by the client to claim a username on the server. When there is already a
     * client logged in with this username, the server should respond with
     * ALREADYLOGGEDIN, and the client should try a different username. Otherwise,
     * the server will respond with LOGIN.
     *
     * @param user username of the client.
     * @return true if the message is sent successfully.
     */
    @Override
    public boolean login(String user) {
        String filteredUsername = user.replace("~", "");
        System.out.println("[CLIENT]" + "LOGIN~" + filteredUsername);
        setUsername(filteredUsername);
        out.println("LOGIN~" + filteredUsername);
        out.flush();
        return true;
    }

    @Override
    public void help() {
        String help = "LIST OF POSSIBLE COMMANDS -> \"HELP\", \"LIST\"," +
                " \"QUEUE\"" + ", \"PING\", \"QUIT\"";
        System.out.println(help);
    }

    /**
     * Sent by a client to request a list of clients who are currently logged into the server.
     * Allowed at any point once the client himself has logged in.
     */
    @Override
    public void list() {
        out.println("LIST");
        out.flush();
    }

    /**
     * Sent by the client to indicate that it wants to participate in a game.
     * The server will place the client at the back of the queue of waiting players.
     * When the command is issued a second time, the client is removed from the queue.
     */
    @Override
    public void queue() {
        out.println("QUEUE");
        out.flush();
    }

    /**
     * Parser for changing the rotation index from the client input to the server protocol.
     * @param rotation String input from the user.
     * @return valid rotation for the communication protocol.
     */
    @Override
    public int parseRotation(String rotation) {
        switch (rotation) {
            case "1-":
                return 0;
            case "1+":
                return 1;
            case "2-":
                return 2;
            case "2+":
                return 3;
            case "3-":
                return 4;
            case "3+":
                return 5;
            case "4-":
                return 6;
            case "4+":
                return 7;
        }
        return -1;
    }

    /**
     * Sent by the client to make a move on the in-game board.
     * Only allowed when it is the player's turn.
     */
    @Override
    public void move(String input) {

        //Because the AI is programmed to only pick valid moves, another verification
        //for the validity of the move is not really needed here.

        String[] inArray = input.split("\\s+");
        String rotation = "";
        //get move and rotation from input
        if (inArray.length == 2) {
            move = Integer.parseInt(inArray[0]);
            rotation = inArray[1];
        }
        if (inArray.length != 2 || !board.isValidMove(board, move)) {
            System.out.println("Invalid arguments given to command move." +
                    " Use " + "move + rotation");
            String nextInput = sc.nextLine();
            move(nextInput);
        }
        //parse the rotation
        int parsedRotation;
        if (board.isValidRotation(parseRotation(rotation))) {
            parsedRotation = parseRotation(rotation);
        } else {
            throw new ArrayIndexOutOfBoundsException("Invalid rotation");
        }


        //send the input to the server
        out.println("MOVE~" + move + "~" + parsedRotation);
        out.flush();

    }

    /**
     * Sent by client. The other party must immediately return a PONG message.
     */
    @Override
    public void ping() {
        out.println("PING");
        out.flush();
        //check if you get pong
    }

    /**
     * Sent by client in response to PING.
     */
    @Override
    public void pong() {
        out.println("PONG");
        out.flush();
    }

    /**
     * Sent by client to ask the other party to disconnect.
     */
    @Override
    public void quit() {
        out.println("QUIT");
        out.flush();
        close();
    }


    /**
     * Parse the received input from the server. Checks individual cases of the received input.
     *
     * @param input The string received from the server.
     */
    private void parseServerInput(String input) {

        if (input == null) {
            return;
        } else if (input.equals("QUIT")) {
            System.err.println("You have been kicked out of the server for inactivity.");
            close();
        } else if (input.startsWith("NEWGAME")) {
            System.out.println(input);
            String[] inArray = input.split("~");
            String user1 = inArray[1];
            String user2 = inArray[2];
            if (user1.equals(username)) {
                //This means that I start first.
                x = 1;
                clientInputParsing.naiveAiMove();
            } else {
                x = 0;
            }
        } else if (input.contains("MOVE")) {
            //I use this x variable to switch turns in between players on the client side.
            x = (x + 1) % 2;
            String[] inArray = input.split("~");
            int index = Integer.parseInt(inArray[1]);
            int rotation = Integer.parseInt(inArray[2]);
            if (x == 1) {
                if (board.isEmptyField(index)) {
                    board.setField(index, Marble.BLACK);
                    rotationParsing.parseRotationFromServer(rotation, board);
                    System.out.println("Opponent's move: \n");
                    System.out.println("\n" + board);
                    clientInputParsing.naiveAiMove();
                } else {
                    System.out.println("The opponent's move is illegal!");
                }
            } else if (x == 0) {
                if (board.isEmptyField(index)) {
                    board.setField(index, Marble.WHITE);
                    rotationParsing.parseRotationFromServer(rotation, board);
                    System.out.println("Your move: \n");
                    System.out.println("\n" + board);
                } else {
                    System.out.println("Your move is illegal!");
                }
            }
        } else if (input.startsWith("LOGIN")) {
            System.out.println(input);
            if (!inGame) {
                inGame = true;
                queue();
            }
        } else if (input.equals("PING")) {
            System.out.println(input);
            pong();
        } else if (input.equals("ALREADYLOGGEDIN")) {
            System.err.println("The user is already logged in to the server. Connection closing.");
            close();
            System.exit(0);
        } else if (input.isEmpty()) {
            System.out.println("The server has sent NULL. Connection closing");
            quit();
        } else if (input.contains("ERROR")) {
            System.out.println("An error has occurred!.");
            System.out.println(input);
        } else if (input.contains("GAMEOVER") || input.contains("DISCONNECTED")) {
            inGame = false;
            board.clearBoard();
            System.out.println(input);
            queue();
        } else {
            if (!input.startsWith("MOVE")) {
                System.out.println(input);
            }
        }
    }

    //GETTERS

    public Board getBoard() {
        return board;
    }

    //SETTERS

    /**
     * Sets the username of the current client (when logged in).
     */
    public void setUsername(String username) {
        this.username = username;
    }

    /**
     * Sleeps the current thread for 1/2 a second in order to slow down the
     * speed at which messages are sent.
     */
    private void waitHalfASecond() {
        try {
            Thread.sleep(500);
        } catch (InterruptedException e) {
            System.err.println("Could not sleep the thread.");
        }
    }

    @Override
    public void run() {
        try {
            while (!socket.isClosed()) {
                String input = in.readLine();
                parseServerInput(input);
            }
        } catch (IOException e) {
            System.err.println("Client disconnected");
        }
    }
}
