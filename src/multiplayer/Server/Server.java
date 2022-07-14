package multiplayer.Server;

import game.Board;
import game.Marble;
import multiplayer.Exceptions.NoClientConnectedException;

import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;


/**
 * Server implementation for the Pentago Project.
 */
public class Server implements ServerInterface, Runnable {

    private ServerSocket serverSocket;
    private Map<ClientHandler, String> clientMap;
    private final Queue<ClientHandler> playerQueue = new ArrayDeque<>();
    private final Scanner sc = new Scanner(new InputStreamReader(System.in));
    Map<ClientHandler, String> tempMatchList;

    //METHODS

    /**
     * Starts the server using the given port.
     */
    @Override
    public void start(int port) {
        try {
            System.out.println("Please input a host-IP address. For localhost, press enter:");
            String input = sc.nextLine();
            if (input.isEmpty() || input.isBlank()) {
                serverSocket = new ServerSocket(port);
            } else {
                serverSocket = new ServerSocket(port, 30, InetAddress.getByName(input));
            }
            clientMap = new HashMap<>();
            System.out.println("Pentago server started on " + serverSocket.getInetAddress() +
                    ":" + serverSocket.getLocalPort());
            Thread serverThread = new Thread(this);
            serverThread.start();
        } catch (IOException e) {
            System.err.println("The server could not be started!");
        }
    }

    public void startTest(int port) {
        try {

            serverSocket = new ServerSocket(port);
            clientMap = new HashMap<>();
            System.out.println("Pentago server started on " + serverSocket.getInetAddress() +
                    ":" + serverSocket.getLocalPort());
            Thread serverThread = new Thread(this);
            serverThread.start();
        } catch (IOException e) {
            System.err.println("The server could not be started!");
        }
    }

    /**
     * Checks whether the connection is alive. If it is, it returns the port number of the socket.
     *
     * @return port number
     */
    @Override
    public int getPort() {
        return serverSocket.getLocalPort();
    }

    /**
     * Stops the server by disconnecting all clients and closing the socket.
     */
    @Override
    public void stop() {
        if (!serverSocket.isClosed()) {
            try {
                System.out.println("Pentago server has been closed");
                serverSocket.close();
            } catch (IOException e) {
                System.err.println("The server could not be closed!");
            }

        }
    }


    /**
     * Adds a player to the waiting queue if he is not there already.
     *
     * @param ch Player to be added to the queue.
     */

    protected synchronized void addToPlayerQueue(ClientHandler ch) {
        if (!playerQueue.contains(ch)) {
            playerQueue.add(ch);
        }
        if (playerQueue.size() > 1) {
            tempMatchList = getMatchUp();
            GameHandler gameHandler = new GameHandler(tempMatchList, new Board(), this);
            List<String> names = getGivenClientNames(tempMatchList);
            for (ClientHandler client :
                    tempMatchList.keySet()) {
                client.sendCommandToPlayer("NEWGAME~" + names.get(0) + "~" + names.get(1));
                if (client.getClientName().equals(names.get(0))) {
                    client.setMarble(Marble.WHITE);
                    client.setMyTurn(true);
                } else if (client.getClientName().equals(names.get(1))) {
                    client.setMarble(Marble.BLACK);
                }
                client.startGame(gameHandler);

            }
        }
    }

    /**
     * Removes a player from the waiting queue.
     *
     * @param ch Player to be removed from the queue
     */
    protected synchronized void removeFromPlayerQueue(ClientHandler ch) {
        playerQueue.remove(ch);
    }

    /**
     * Takes two players (that are logged-in) and adds them to a list.
     *
     * @return list of the 2 players
     */
    protected synchronized Map<ClientHandler, String> getMatchUp() {
        Map<ClientHandler, String> clientPair = new HashMap<>();

        if (playerQueue.size() > 1) {
            ClientHandler ch1 = playerQueue.poll();
            ClientHandler ch2 = playerQueue.poll();
            clientPair.put(ch1, ch1.getClientName());

            assert ch2 != null;
            clientPair.put(ch2, ch2.getClientName());
        }
        return clientPair;
    }


    /**
     * Goes through the map holding all the client handlers and makes a list of their names.
     *
     * @return client name list
     * @throws NoClientConnectedException if no client is connected
     */
    protected synchronized List<String> getClientNameList() throws NoClientConnectedException {
        if (!serverSocket.isClosed()) {
            List<String> clientNames = new ArrayList<>();
            for (ClientHandler ch :
                    clientMap.keySet()
            ) {
                clientNames.add(ch.getClientName());
            }
            return clientNames;
        }
        throw new NoClientConnectedException();
    }

    /**
     * Retrieves the names of the clients in the given map.
     * @param map includes the players and their names.
     * @return their names in a list.
     */
    protected synchronized List<String> getGivenClientNames(Map<ClientHandler, String> map) {
        List<String> names = new ArrayList<>();
        for (ClientHandler ch:
             map.keySet()) {
            names.add(ch.getClientName());
        }
        return names;
    }

    /**
     * Retrieves the map which includes all the clients on the server.
     * @return map containing all the clients.
     */
    public synchronized Map<ClientHandler, String> getClientMap() {
        return clientMap;
    }

    /**
     * Checks whether the given client and clientName exists in the list of clients. If it does,
     * remove him. - Called when a client disconnects.
     *
     * @param ch ClientHandler that handles the given client
     */
    protected synchronized void removeClient(ClientHandler ch) {
        clientMap.remove(ch);
    }

    /**
     * Adds a client to the server client-list.
     * @param ch Client to be added.
     */
    protected synchronized void addClient(ClientHandler ch) {
        clientMap.put(ch, null);
    }

    public boolean isAlive() {
        return !serverSocket.isClosed();
    }

    @Override
    public void run() {
        try {
            while (!serverSocket.isClosed()) {
                //FIELDS
                Socket clientSocket = serverSocket.accept();
                ClientHandler clientHandler = new ClientHandler(clientSocket, this);
                addClient(clientHandler);
                Thread clientHandlerThread = new Thread(clientHandler);
                clientHandlerThread.start();
            }
        } catch (IOException e) {
            System.err.println("The connection with the client could not be established.");
        }
    }
}
