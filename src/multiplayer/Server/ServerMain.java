package multiplayer.Server;

/**
 * Main class for the server of the Pentago Project.
 */
public class ServerMain {

    private static final int PORT = 6969;

    public static void main(String[] args) {
        Server server = new Server();
        server.start(PORT);
    }
}
