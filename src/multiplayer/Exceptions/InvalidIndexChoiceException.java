package multiplayer.Exceptions;

/**
 * Exception that is thrown whenever an index choice is invalid.
 */
public class InvalidIndexChoiceException extends Exception {

    @Override
    public String getMessage() {
        return "ERROR~Invalid index choice!";
    }
}
