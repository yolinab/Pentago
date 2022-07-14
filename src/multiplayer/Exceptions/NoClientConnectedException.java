package multiplayer.Exceptions;

/**
 * Exception that is thrown whenever a client/server requests a list
 * of users and there are none connected.
 */
public class NoClientConnectedException extends Exception {

    @Override
    public String getMessage() {
        return "ERROR";
    }
}
