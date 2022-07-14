package multiplayer.Exceptions;

/**
 * Exception that is thrown whenever a client tries to do an invalid login.
 */
public class InvalidUsernameException extends Exception {

    @Override
    public String getMessage() {
        return "ERROR~Received LOGIN message with invalid number of parameters!";
    }
}
