package ai;

import game.Board;
import game.Marble;

import java.util.Random;

/**
 * Naive AI implementation for the Pentago Project. This AI was designed to only input random
 * moves and rotations. It is the equivalent of the "EASY" difficulty bots.
 */
public class NaiveAI implements AI {

    /**
     * Gets the name of the AI.
     * @return name
     */
    @Override
    public String getName() {
        return "NaiveAI";
    }

    /**
     * Determines the next move. In this case, it makes a move on a random empty index.
     * @param board the board on which the AI plays.
     * @param marble the marble with which the AI plays.
     * @return a valid move.
     */
    @Override
    public int determineMove(Board board, Marble marble) {
        while (true) {
            int randomIdx = new Random().nextInt(Board.getDIM() * Board.getDIM());
            if (board.isEmptyField(randomIdx)) {
                return randomIdx;
            }
        }
    }

    /**
     * Determines a rotation. In this case, it makes a random rotation.
     * @param board the board on which the AI plays.
     * @return a random rotation.
     */
    @Override
    public int determineAiRotation(Board board) {
        int[] rotations = new int[]{1, 2, 3, 4, 5, 6, 7, 8};
        int randomIdx = new Random().nextInt(7);
        return rotations[randomIdx];
    }
}
