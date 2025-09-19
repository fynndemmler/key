//import java.util.UUID;
import java.util.List;
import java.util.*;

enum Coin {
    HEADS,
    TAILS
}

enum State {
    IDLE,
    GAME_AVAILABLE,
    BET_PLACED
}

enum Methods {
    TRANSFER,
    REMOVE_FROM_POT,
    CREATE_GAME,
    PLACE_BET,
    DECIDE_BET
}

class Address {
    int id;
    int balance;

    public Address(int id, int balance) {
        this.id = id;
        this.balance = balance;
    }
}

/*
    Note that a falsey return value for any method in this class reflects aborted execution.
 */
class Casino {
    public Address operator;
    public Address player;
    public Coin guess;
    public int pot;
    public int hashedNumber;
    public int bet;
    private State state;

    public Casino(Address operator, Address player) {
        this.operator = operator;
        this.player = player;
        state = State.IDLE;
        pot = 0;
        bet = 0;
    }

    /*
       requires operator != null & player != null;
       ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(placeBet, true))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(removeFromPot, true))\then(TRUE)\else(FALSE))))*);
      diverges false; */
    public static void allNonReoccuringMethodCallSequencesGame() {
        Address operator = new Address(1, 100);
        Address player = new Address(2, 100);
       Casino casino = new Casino(operator, player);
       // Every single method call sequence should at least occur once (n * fac(n))
       int[] methods = new int[]{Methods.TRANSFER, Methods.REMOVE_FROM_POT, Methods.CREATE_GAME, Methods.PLACE_BET, Methods.DECIDE_BET};
       //var method_sequences = permute(methods);
       Methods[] method_sequences = new Methods[]{Methods.TRANSFER, Methods.CREATE_GAME, Methods.PLACE_BET, Methods.REMOVE_FROM_POT, Methods.DECIDE_BET};
       int c = 0;
       //for (List<Integer> method_sequence : method_sequences) {
       for (Integer method : method_sequences) {
           if (method == Methods.TRANSFER) {
               casino.transfer(operator, 10);
           } else if (method == Methods.REMOVE_FROM_POT) {
               casino.removeFromPot(operator, 5);
           } else if (method == Methods.CREATE_GAME) {
               casino.createGame(operator, 1337);
           } else if (method == Methods.PLACE_BET) {
               Coin guess = c % 2 == 0 ? Coin.HEADS : Coin.TAILS;
               casino.placeBet(player, 10, guess);
           } else if (method == Methods.DECIDE_BET) {
               casino.decideBet(operator, 1337);
           }
           c = c + 1;
       }
       //}
    }

    /*
       Transfer money from an address. The money is just added to the pot and this abstract method
       simply reflects the transfer call from the original Casino contract. It has no effect on
       verification.
     */
    public boolean transfer(Address caller, int amount) {
        caller.balance = caller.balance - amount;
        return true;
    }

    // Remove money from pot
    public boolean removeFromPot(Address caller, int amount) {
        // no active bet ongoing:
        if (this.state == State.BET_PLACED || caller != operator) {
           return false;
        }
        transfer(caller, amount);
        pot = pot - amount;
        return true;
    }

    // Operator opens a bet.
    public boolean createGame(Address caller, int hashedNumber) {
        if (state != State.IDLE || caller != operator) {
            return false;
        }
        this.hashedNumber = hashedNumber;
        state = State.GAME_AVAILABLE;
        return true;
    }

    // Player places a bet
    public boolean placeBet(Address caller, int value, Coin guess) {
        if (state != State.GAME_AVAILABLE || caller == operator || value > pot) {
            return false;
        }
        state = State.BET_PLACED;
        player = caller;
        bet = value;
        this.guess = guess;
        return true;
    }

    // Operator resolves a bet
    public boolean decideBet(Address caller, int secretNumber) {
        if (state != State.BET_PLACED || caller != operator || hashedNumber != secretNumber) {
            return false;
        }
        Coin secret = (secretNumber % 2 == 0) ? Coin.HEADS : Coin.TAILS;

        if (secret == guess) {
            // player wins, gets back twicer her bet
            pot = pot - bet;
            transfer(player, 2*bet);
            bet = 0;
        } else {
            // operator wins, bet trasnfered to pot
            pot = pot + bet;
            bet = 0;
        }
        state = State.IDLE;
        return true;
    }
}