package game;

/**
 * Abstract class for creating a player for the Pentago game.
 * @author Vlad Gosa and Yolina Yordanova
 */
public abstract class Player {

    //Instance variables

    private String name;
    private final Marble marble;

    //Constructors

    /**
     * Creates a new player object
     * @param marble the chosen marble.
     * @param name of the player.
     */
    /*@ requires name != null;
        requires marble == Marble.BLACK || marble == Marble.WHITE;
        ensures this.name == name;
        ensures this.marble == marble;
    @*/
    protected Player(String name, Marble marble) {
        this.name = name;
        this.marble = marble;
    }

    protected Player(Marble marble) {
        this.marble = marble;
    }

    //Queries

    /**
     *
     * @return Name of the player
     */
    public String getName() {
        return name; }

    /**
     *
     * @return Marble of the player
     */
    public Marble getMarble() {
        return marble; }

    /**
     *Determines the field for the next move.
     * @param board the current game board
     * @return the player's choice
     */
    /*@ requires board != null && board.isFull() == false;
        ensures board.isField(\result) && board.getField(\result) == Marble.EMPTY;
    @*/
    public abstract int determineMove(Board board);

    /**
     * Determine the rotation after the marble has been placed
     * @param board the current game board
     */
    /*@ requires board!= null && board.isFull() == false;
    @*/
    public abstract void determineRotation(Board board);

    //commands
    /**
     * Makes a move on the board.
     * @param board the current board
     */
    //@ requires board != null && board.isFull() == false;
    public void makeMove(Board board) {
        int choice = determineMove(board);
        board.setField(choice, getMarble());
    }
}
