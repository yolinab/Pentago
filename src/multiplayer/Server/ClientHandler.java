package multiplayer.Server;

import game.Board;
import game.Marble;
import multiplayer.Exceptions.*;
import multiplayer.Parsers.RotationParsing;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;
import java.time.LocalTime;

/**
 * ClientHandler class is a helper-class used to handle communications between
 * the server and the client that connects to the Pentago server.
 * Every time a connection is made, a new thread is created and started in the Server
 * class which invokes this class.
 */
public class ClientHandler implements Runnable {

    private final Socket socket;
    private final Server server;
    private final LocalTime localTime = LocalTime.now();
    private final RotationParsing rotationParsing = new RotationParsing();
    private PrintWriter out;
    private String clientName;
    private boolean helloStatus = false;
    private boolean loginStatus = false;
    private boolean inGameStatus = false;
    private boolean inQueueStatus = false;
    private boolean myTurn = false;
    private Marble marble;
    private GameHandler gameHandler;


//CONSTRUCTOR

    public ClientHandler(Socket socket, Server server) {
        this.socket = socket;
        this.server = server;
    }
////////////////////////////////////////////////////////////////////////////////////////////////////

    /**
     * Closes the connection with the client.
     */
    private void close() {
        try {
            out.println("CONNECTION CLOSED");
            out.flush();
            server.removeClient(this);
            if (inQueueStatus) {
                server.removeFromPlayerQueue(this);
            }
            if (inGameStatus) {
                gameHandler.checkPlayerWinByDisconnect();
            }
            socket.close();
        } catch (IOException e) {
            System.err.println("The connection with the client could not be closed.");
        }
    }


    /**
     * Sends a command to the client handled by this client handler.
     * @param input The string to be sent.
     */
    protected void sendCommandToPlayer(String input) {
        out.println(input);
        out.flush();
    }

    /**
     * Sets the status of the clientHandler to "in game" and assigns a GameHandler object to it.
     * @param givenGameHandler the given gameHandler.
     */
    protected void startGame(GameHandler givenGameHandler) {
        inGameStatus = true;
        this.gameHandler = givenGameHandler;
    }

    /**
     * Parses the input coming from the client and sends back an appropriate message according
     * to the protocol.
     * @param input the given input.
     */
    private void parseInput(String input) {

        if (input == null) {
            close();
            return;
        }

        //HELLO
        if (input.startsWith("HELLO~")) {
            if (!helloStatus) {
                out.println("HELLO~Vlad's Magnificent Server");
                out.flush();
                helloStatus = true;
            }
            //LOGIN
        } else if (input.startsWith("LOGIN~")) {
            if (!loginStatus) {
                String[] inputArr = input.split("~");
                try {
                    if (inputArr.length <= 1 || inputArr[1].equals("") || inputArr[1].isEmpty()) {
                        throw new InvalidUsernameException();
                    }
                    if (!server.getClientNameList().contains(inputArr[1])) {
                        clientName = inputArr[1];
                        out.println("LOGIN");
                        out.flush();
                        loginStatus = true;
                        //Print out the time at which a client successfully logged in.
                        System.out.println("[" + localTime + "]" + "Client " + clientName
                                + " has logged in to the server");
                    } else {
                        out.println("ALREADYLOGGEDIN");
                        out.flush();
                    }
                } catch (NoClientConnectedException e) {
                    System.err.println(e.getMessage());
                } catch (InvalidUsernameException e) {
                    out.println(e.getMessage());
                    out.flush();
                    close();
                }
            }
            //PING
        } else if (input.equals("PING")) {
            out.println("PONG");
            out.flush();

            //PONG
        } else if (input.equals("PONG")) {
            System.out.println(input);

            //LIST
        } else if (input.equals("LIST")) {
            try {
                if (loginStatus) {
                    out.println(server.getClientNameList());
                    out.flush();
                } else {
                    throw new ClientNotLoggedInException();
                }
            } catch (NoClientConnectedException | ClientNotLoggedInException e) {
                System.out.println("<CLIENT>" + e.getMessage());
                close();
            }

            //QUIT
        } else if (input.equals("QUIT")) {
            close();

            //QUEUE
        } else if (input.equals("QUEUE")) {
            if (!loginStatus) {
                close();
            } else {
                if (!inQueueStatus) {
                    server.addToPlayerQueue(this);
                    inQueueStatus = true;
                } else {
                    server.removeFromPlayerQueue(this);
                    inQueueStatus = false;
                }
            }

            //MOVE

        } else if (input.startsWith("MOVE~")) {
            if (inGameStatus && myTurn) {
                try {
                    String[] inArray = input.split("~");
                    if (inArray.length == 3) {
                        int index = Integer.parseInt(inArray[1]);
                        int rotation = Integer.parseInt(inArray[2]);
                        if (!gameHandler.getBoard().isValidMove(gameHandler.getBoard(), index)) {
                            throw new InvalidIndexChoiceException();

                        } else if (!gameHandler.getBoard().isValidRotation(rotation)) {
                            throw new InvalidRotationChoiceException();
                        } else {
                            //all good, the moves are confirmed correct
                            if (marble.equals(Marble.WHITE)) {
                                gameHandler.synchronizeBoard(index, rotation, marble);
                            } else if (marble.equals(Marble.BLACK)) {
                                gameHandler.synchronizeBoard(index, rotation, marble);
                            }
                            //if the board has a winner
                            if (gameHandler.getBoard().hasWinner()) {
                                gameHandler.sendMoveToPlayers(input);
                                gameHandler.sendMoveToPlayers("GAMEOVER~VICTORY~" + clientName);
                                gameHandler.resetQueueStatus();
                                //if the board is full
                            } else if (gameHandler.getBoard().isFull()) {
                                gameHandler.sendMoveToPlayers(input);
                                gameHandler.sendMoveToPlayers("GAMEOVER~DRAW");
                                gameHandler.resetQueueStatus();
                                //switch the turns after a move has been made.
                            } else {
                                gameHandler.switchTurns();
                                waitHalfASecond();
                                gameHandler.sendMoveToPlayers(input);
                            }
                        }
                    }
                } catch (InvalidIndexChoiceException | InvalidRotationChoiceException e) {
                    out.println(e.getMessage());
                    out.flush();
                }
            }

        }
    }

    //GETTERS

    /**
     * Getter for the username of the client.
     * @return username
     */
    public String getClientName() {
        return clientName;
    }

    /**
     * Getter for the queue status of the player.
     * @return true if in queue, false otherwise.
     */
    public Boolean getInQueueStatus() {
        return inQueueStatus;
    }

    /**
     * Getter for the board used in the game.
     * @return the board used by the GameHandler class.
     */
    public Board getBoard() {
        return gameHandler.getBoard();
    }

    /**
     * Getter for the marble used by the client.
     * @return marble
     */
    public Marble getMarble() {
        return marble;
    }

    /**
     * Getter for the turn of the client.
     * @return true if it is his turn, false otherwise.
     */
    public boolean isMyTurn() {
        return myTurn;
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////

    //SETTERS

    /**
     * Setter for the marble of the client.
     * @param marble the given marble.
     */
    protected void setMarble(Marble marble) {
        this.marble = marble;
    }

    /**
     * Setter for the turn of the client.
     * @param value boolean
     */
    public void setMyTurn(boolean value) {
        myTurn = value;
    }

    /**
     * Resets the queue status of the player (switches to false / out of queue).
     */
    protected void resetInQueueStatus() {
        inQueueStatus = false;
        inGameStatus = false;
    }

    ///////////////////////////////////////////////////////////////////////////////////////////////

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
            //If there is no input for 5 minutes, the client will be kicked out of the server.
            socket.setSoTimeout(300000);
            while (!socket.isClosed()) {
                BufferedReader in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                out = new PrintWriter(socket.getOutputStream());
                String input = in.readLine();
                parseInput(input);
            }
        } catch (IOException e) {
            out.println("QUIT");
            out.flush();
            LocalTime localTimeExit = LocalTime.now();
            System.err.println("[" + localTimeExit + "]" + "Client " +
                    clientName + " has disconnected from the server");
            try {
                if (inQueueStatus) {
                    server.removeFromPlayerQueue(this);
                }
                server.removeClient(this);
            } finally {
                if (inGameStatus) {
                    gameHandler.checkPlayerWinByDisconnect();
                }
            }
        }
    }
}