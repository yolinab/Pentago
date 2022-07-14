package game;


import java.util.Scanner;

/**
 * Class for maintaining the Pentago local game. !(It is only used for the local games / testing).
 * @author Vlad Gosa and Yolina Yordanova
 */
public class Game {
    //@ private invariant board != null;

    private static final int NUMBER_PLAYERS = 2;
    private int moveChoice;
    private String rotationChoice;

    /**
     * The board.
     */
    private final Board board;

    /*@ private invariant players.length == NUMBER_PLAYERS;
        private invariant (\forall int i; (i >= 0 && i < NUMBER_PLAYERS); players[i] != null);
    @*/
    /**
     * The 2 players of the game.
     */
    private final Player[] players;

    /**
     * Index of the current player.
     */

    private int current;

    //Constructors

    /**
     * Creates a new Game object.
     * @param s0 the first player
     * @param s1 the second player
     */
    //@ requires s0 != null && s1 != null;
    public Game(Player s0, Player s1) {
        board = new Board();
        players = new Player[NUMBER_PLAYERS];
        players[0] = s0;
        players[1] = s1;
        current = 0;
    }

    //Commands

    /**
     * Starts the Pentago game.
     * Asks after each ended game if the user want to continue. Continues until
     * the user does not want to play anymore.
     */
//    public void start() {
//        Scanner sc = new Scanner(System.in);
//        boolean continueGame = true;
//        while (continueGame) {
//            reset();
//            play();
//            System.out.println("\n> Play another time? (y/n)?");
//            String input = sc.nextLine();
//            while (!(input.equals("y") || input.equals("n"))) {
//                input = sc.nextLine();
//            }
//            if (input.equals("y")) {
//                continueGame = true;
//            } else {
//                continueGame = false;
//            }
//        }
//    }

    //For the purpose of our testing, part of this code has been commented out so that we can
    //test only one game.
    public void start() {
        Scanner sc = new Scanner(System.in);
        boolean continueGame = true;
        while (continueGame) {
            reset();
            play();
            continueGame = false;
        }
    }

    /**
     * Resets the game.
     * The board is emptied and player[0] becomes the current player.
     */
    public void reset() {
        current = 0;
        board.clearBoard();

    }

    /**
     * Plays the Pentago game.
     * First the (still empty) board is shown. Then the game is played
     * until it is over. Players can make a move one after the other.
     * After each move, the changed game situation is printed.
     */
    private void play() {
        update();
        int x = 1;
        while (!board.gameOver())   {
            x = (x + 1) % 2;
            int move = players[x].determineMove(board);
            board.setField(move, players[x].getMarble());
            update();
            players[x].determineRotation(board);
            update();
            board.isWinner(players[x].getMarble());

        }
        printResult();
    }

    /**
     * Prints the game situation.
     */
    private void update() {
        System.out.println("\ncurrent game situation: \n\n" + board.toString()
                + "\n");
    }

    /**
     * Prints the result of the last game.
     */
    //@ requires board.hasWinner() || board.isFull();
    private void printResult() {
        if (board.hasWinner()) {
            Player winner = board.isWinner(players[0].getMarble()) ? players[0]
                    : players[1];
            System.out.println("Player " + winner.getName() + " ("
                    + winner.getMarble().toString() + ") has won!");
        } else {
            System.out.println("Draw. There is no winner!");
        }
    }

    public void setMoveChoice(int moveChoice) {
        this.moveChoice = moveChoice;
    }

    public void setRotationChoice(String rotationChoice) {
        this.rotationChoice = rotationChoice;
    }

    public int getMoveChoice() {
        return moveChoice;
    }

    public String getRotationChoice() {
        return rotationChoice;
    }

    public Board getBoard() {
        return board;
    }
}
