package multiplayer.Exceptions;

/**
 * Exception that is thrown whenever a client does an Illegal move.
 */
public class IllegalMoveException extends Exception {

    @Override
    public String getMessage() {
        return "Invalid move! Please try again using the MOVE command.";
    }
}
