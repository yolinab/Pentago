package multiplayer.Exceptions;

/**
 * Exception thrown whenever an input from the user does not match any rotational command.
 */
public class InvalidRotationChoiceException extends Exception {

    @Override
    public String getMessage() {
        return "ERROR~Invalid rotation choice!";
    }
}
