package ai;

import game.Board;
import game.Marble;
import game.Player;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

/**
 * SmartAI class for the Pentago Project.
 * @author Yolina Yordanova
 */
public class SmartAI extends Player {

    private final static int DEPTH = 2;
    private final Marble marble;
    private HashMap<Integer, Integer> opponentWinningMove;
    private HashMap<Integer, Integer> aiWinningMoves;
    private int move;
    private int rotation;
    private Board optimalBoard;

    //@requires marble == marble.WHITE && marble == marble.BLACK;
    public SmartAI(Marble marble) {
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
        int tempRotation = rotation;
        return tempRotation;
    }

    /*@ requires board != null && board.isFull() == false;
        ensures board.isField(\result) && board.getField(\result) == Marble.EMPTY;
        ensures \result instanceof int;
    @*/
    @Override
    public int determineMove(Board board) {


        board.getAllCurrentPossibleBoards(marble);
        HashMap<Integer, Integer> currentWinningMoves = board.getWinningMoves();
        aiWinningMoves = currentWinningMoves;
        if (!currentWinningMoves.isEmpty()) {
            ArrayList<Integer> winningPlacements = new ArrayList<>(currentWinningMoves.keySet());
            move = winningPlacements.get(0);
            rotation = currentWinningMoves.get(move);
            // System.out.println("AI has decided that to win, has to place marble at: " + move);
            //System.out.println("And to win, has to rotate index: " + rotation);
            return move;
        }

        /*
        if the AI doesn't have a next move win call the minimax and evaluate which is the best board
        when minmax is called it sets the local optimalBoard based on it's score,
        and from that board we get it's corresponding move
        */
        int score = minimax(board, marble, DEPTH, true);
        if (score != 0) {
            ArrayList<Board> possibleBoards = board.getAllCurrentPossibleBoards(marble);
            for (Board nextBoard : possibleBoards) {
                if (nextBoard.evaluateScore(marble) == score) {
                    optimalBoard = nextBoard;
                    move = optimalBoard.getMoveMade().get(0);
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

            for (Map.Entry<Integer, Integer> moveCombination : aiWinningMoves.entrySet()) {
                if (moveCombination.getKey().equals(move)) {
                    rotation = moveCombination.getValue();
                    board.rotate(rotation);
                    return;
                }
            }
        }

        //the minmax rotation

        int score = minimax(board, marble, DEPTH, true);
        if (score != 0) {
            ArrayList<Board> possibleBoards = board.getAllCurrentPossibleBoards(marble);
            for (Board nextBoard : possibleBoards) {
                if (nextBoard.evaluateScore(marble) == score) {
                    rotation = optimalBoard.getMoveMade().get(1);
                    break;

                }
            }
        }
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
            if (optimalScore > optimalScore && depth == SmartAI.DEPTH - 1) {
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
                //here determines the score of all the boards at the bottom of the tree,
                // being the opponents turn minimizing player returns the board that leads to
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

