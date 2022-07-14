package ai;

import game.Board;
import game.Marble;
import game.Player;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

/**
 * SmartAIWithHints class for the Pentago Project.
 * @author Yolina Yordanova
 */
public class SmartAIWithHints extends Player {

    private final static int DEPTH = 2;
    private final Marble marble;
    private HashMap<Integer, Integer> opponentWinningMove;
    private HashMap<Integer, Integer> aiWinningMoves;
    private int move;
    private int rotation;
    private Board optimalBoard;

    //@requires marble == marble.WHITE && marble == marble.BLACK;
    public SmartAIWithHints(Marble marble) {
        super(marble);
        this.marble = marble;
    }

    //@ensures \result instanceof String;
    //@ensures \result.equals(getName() + "-" + getMarble().toString());
    public String getName() {
        return "Smart" + "-" + getMarble().toString();
    }

    //@ensures marble == marble.WHITE && marble == marble.BLACK;
    public Marble getMarble() {
        return marble;
    }

    //@ensures marble == marble.WHITE && marble == marble.BLACK;
    public Marble getOpponentMarble() {
        if (marble.equals(Marble.WHITE)) {
            return Marble.BLACK;
        }
        return Marble.WHITE;
    }

    public int sendRotation() {
        return rotation;
    }

    /*@ requires board != null && board.isFull() == false;
        ensures board.isField(\result) && board.getField(\result) == Marble.EMPTY;
        ensures \result instanceof int;
    @*/
    @Override
    public int determineMove(Board board) {
        //if the opponent doesn't have a next move win,
        // check if AI has a next move win and place marble there

        board.getAllCurrentPossibleBoards(marble);
        HashMap<Integer, Integer> currentWinningMoves = board.getWinningMoves();
        aiWinningMoves = currentWinningMoves;
        if (!currentWinningMoves.isEmpty()) {
            ArrayList<Integer> winningPlacements = new ArrayList<>(currentWinningMoves.keySet());
            move = winningPlacements.get(0);
            rotation = currentWinningMoves.get(move);
            System.out.println("AI has decided that to win, has to place marble at: " + move);
            System.out.println("And to win, has to rotate index: " + rotation);
            return move;
        }

        /*
        if the AI doesn't have a next move win call the minimax and evaluate which is the best board
        when minmax is called it sets the local optimalBoard based on it's score,
         and from that board we get it's corresponding move
        */
        int score = minimax(board, marble, DEPTH, true);
        if (score != 0) { //just making sure the minmax doesn't fucking combust
            System.out.println("The score of the current board" +
                    " based on minmax algorithm is: " + score);
            ArrayList<Board> possibleBoards = board.getAllCurrentPossibleBoards(marble);
            for (Board nextBoard : possibleBoards) {
                if (nextBoard.evaluateScore(marble) == score) {
                    optimalBoard = nextBoard;
                    move = optimalBoard.getMoveMade().get(0);
                    System.out.println("Move of the minmax: " + move);
                    break;
                }
            }
        }
        return move;
    }

    public void determineRotation(Board board) {
        //if there was a winning move for the AI, get the rotation corresponding to it from the map
        board.getAllCurrentPossibleBoards(marble);
        aiWinningMoves = board.getWinningMoves();

        this.move = determineMove(board);
        if (!aiWinningMoves.isEmpty()) {
            System.out.println("Amount of winning moves for the AI: " + aiWinningMoves.size());
            System.out.println("Winning rotation index is: " + aiWinningMoves.get(move));

            for (Map.Entry<Integer, Integer> moveCombination : aiWinningMoves.entrySet()) {
                if (moveCombination.getKey().equals(move)) {
                    rotation = moveCombination.getValue();
                    System.out.println("WE DECIDE TO ROTATE TO:  " + rotation);
                    board.rotate(rotation);
                    return;
                }
            }
        }

        //the minmax rotation

        int score = minimax(board, marble, DEPTH, true);
        if (score != 0) {
            System.out.println("The score of the current board" +
                    " based on minmax algorithm is: " + score);
            ArrayList<Board> possibleBoards = board.getAllCurrentPossibleBoards(marble);
            for (Board nextBoard : possibleBoards) {
                if (nextBoard.evaluateScore(marble) == score) {
                    System.out.println("Rotation of the minmax: "
                            + optimalBoard.getMoveMade().get(1));
                    rotation = optimalBoard.getMoveMade().get(1);
                    break;

                }
            }
        }
        System.out.println("Rotation decision the the minmax: " + rotation);
        sendRotation();
        board.rotate(rotation);
    }

    /*@requires board != null && board.isFull() == false && !board.isEmpty();
      @requires marble == marble.WHITE && marble == marble.BLACK;
      @ensures \result != 0;
    */
    private int minimax(Board board, Marble myMarble, int depth, boolean isMaximizingPlayer) {
        int optimalScore = 0;
        //base case
        if (depth == 0) {
            //static evaluation of board
            optimalScore = board.evaluateScore(myMarble);
            return optimalScore;
        }
        if (isMaximizingPlayer) {       //the maximizing player is always the AI
            optimalScore = Integer.MIN_VALUE;
            ArrayList<Board> possibleBoards = board.getAllCurrentPossibleBoards(myMarble);

            for (Board possibleBoard : possibleBoards) {

                //from here goes to minimizing player
                int currentScore = minimax(possibleBoard, myMarble, depth - 1, false);
                if (currentScore > optimalScore) {
                    optimalScore = currentScore;
                }
            }
            if (optimalScore > optimalScore && depth == SmartAIWithHints.DEPTH - 1) {
                optimalScore = optimalScore;
                //to find board with the best score, and it's move
                for (Board boardie : possibleBoards) {
                    ArrayList<Board> boards = boardie.getAllCurrentPossibleBoards(myMarble);
                    for (Board board2 : boards) {
                        if (board2.evaluateScore(myMarble) == optimalScore) {
                            optimalBoard = board2;
                            board2.getAllCurrentPossibleBoards(myMarble);
                            aiWinningMoves = board2.winningMoves;
                            // here determines the moves determined to be best in this situation
                        }
                    }
                }
            }
        } else { //opponent
            optimalScore = Integer.MAX_VALUE;
            ArrayList<Board> possibleBoards = board.getAllCurrentPossibleBoards(myMarble);
            for (Board possBoard : possibleBoards) {
                //here determines the score of all the boards at the
                // bottom of the tree, being the opponents turn
                //minimizing player returns the board that leads to
                // the lowest evaluation (from out point of view)
                int currentScore = minimax(possBoard, myMarble, depth - 1, true);
                if (currentScore < optimalScore) {
                    optimalScore = currentScore;
                }
            }
        }
        return optimalScore;
    }
}