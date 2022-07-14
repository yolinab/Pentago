package multiplayer.Client.ClientClasses;

/**
 * The interface used for our clients in the Pentago Project.
 */
public interface ClientInterface {

    /**
     * Connects to a compatible server using the given ip/port combination.
     * @param address ip address
     * @param port port number
     */
    void connect(String address, int port);

    /**
     * Closes the connection to the server.
     */
    void close();

    /**
     * The initial message sent by the client once a connection has been established.
     * @param input the initial message
     * @return true if message is sent successfully.
     */
    boolean hello(String input);

    /**
     * Sent by the client to claim a username on the server. When there is already a
     * client logged in with this username, the server should respond with
     * ALREADY_LOGGED_IN, and the client should try a different username. Otherwise,
     * the server will respond with LOGIN.
     * @param username of the client
     * @return true if the message is sent successfully.
     */
    boolean login(String username);

    /**
     * Sent by a client to request a list of clients who are currently logged into the server.
     * Allowed at any point once the client himself has logged in.
     */
    void list();

    /**
     * Sent by the client to indicate that it wants to participate in a game.
     * The server will place the client at the back of the queue of waiting players.
     * When the command is issued a second time, the client is removed from the queue.
     */
    void queue();

    /**
     * Sent by the client to indicate which row(s) or column(s) the player wants to push.
     * Only allowed when it is the player's turn.
     * Syntax: MOVE~(A)~(B)
     * @param input
     */
   // void move(T input);


    /**
     * Sent by client. The other party must immediately return a PONG message.
     */
    void ping();

    /**
     * Sent by client in response to PING.
     */
    void pong();

    /**
     * Sent by client to ask the other party to disconnect.
     */
    void quit();


}
