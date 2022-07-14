package ai;


import game.Board;
import game.Marble;
import game.Player;

/**
 * Class that creates a Player instance of a given AI. !(Used only for local games).
 */
public class ComputerPlayer extends Player {

    private final Marble marble;
    private final AI ai;

    //CONSTRUCTORS

    //@requires marble == marble.WHITE && marble == marble.BLACK;
    public ComputerPlayer(Marble marble, AI ai) {
        super(ai.getName(), marble);
        this.marble = marble;
        this.ai = ai;
    }

    //@requires marble == marble.WHITE && marble == marble.BLACK;
    //@ensures ai instanceof NaiveAI;
    public ComputerPlayer(Marble marble) {
        super("NaiveAI" + "-" + marble.toString(), marble);
        this.marble = marble;
        this.ai = new NaiveAI();
    }

    /**
     *
     * @return the name of the Player.
     */
    //@ensures \result instanceof String;
    //@ensures \result.equals(ai.getName() + "-" + getMarble().toString());
    @Override
    public String getName() {
        return ai.getName() + "-" + getMarble().toString();
    }

    /**
     *Determines the field for the next move.
     * @param board the current game board
     * @return the player's choice
     */
    /*@ requires board != null && board.isFull() == false;
        ensures board.isField(\result) && board.getField(\result) == Marble.EMPTY;
        ensures \result instanceof int;
        ensures \result == ai.determineMove(board, marble);
    @*/
    @Override
    public int determineMove(Board board) {
        return ai.determineMove(board, marble);
    }

    /**
     * Parses the rotation command given by any of the AI's into an actual rotation
     * on the board.
     * @param board the current game board
     */
    public void determineRotation(Board board) {
        switch (ai.determineAiRotation(board)) {
            case 1:
                board.rotateFirstQuadrantClockwise();
                break;
            case 2:
                board.rotateFirstQuadrantAntiClockwise();
                break;
            case 3:
                board.rotateSecondQuadrantClockwise();
                break;
            case 4:
                board.rotateSecondQuadrantAntiClockwise();
                break;
            case 5:
                board.rotateThirdQuadrantClockwise();
                break;
            case 6:
                board.rotateThirdQuadrantAntiClockwise();
                break;
            case 7:
                board.rotateFourthQuadrantClockwise();
                break;
            case 8:
                board.rotateFourthQuadrantAntiClockwise();
                break;
        }
    }

    @Override
    public Marble getMarble() {
        return super.getMarble();
    }

    /**
     * Make a move on the given board.
     * @param board the current board
     */
    @Override
    public void makeMove(Board board) {
        super.makeMove(board);
    }

}