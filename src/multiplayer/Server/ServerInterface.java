package multiplayer.Server;

/**
 * Interface for the server implementation of the Pentago Project.
 */
public interface ServerInterface {

    /**
     * Starts the server using the given port.
     * @param port given port.
     */
    void start(int port);

    /**
     * Checks whether the connection is alive. If it is, it returns the port number of the socket.
     * @return port number
     */
    int getPort();

    /**
     * Stops the server by disconnecting all clients and closing the socket.
     */
    void stop();



}
