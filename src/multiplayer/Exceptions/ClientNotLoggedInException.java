package multiplayer.Exceptions;

/**
 * Exception that is thrown when the client does a command which is not allowed
 * while not being logged in.
 */
public class ClientNotLoggedInException extends Exception {


    @Override
    public String getMessage() {
        return "ERROR~Client is not logged in!";
    }
}
