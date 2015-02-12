{-#LANGUAGE DeriveDataTypeable #-}
{-#LANGUAGE DeriveFunctor #-}
{-#LANGUAGE DeriveFoldable #-}
{-#LANGUAGE DeriveGeneric #-}
{-#LANGUAGE DeriveTraversable #-}
{-#LANGUAGE FlexibleInstances #-}
{-#LANGUAGE GeneralizedNewtypeDeriving #-}
{-#LANGUAGE RankNTypes #-}
{-#LANGUAGE ScopedTypeVariables #-}
{-#LANGUAGE StandaloneDeriving #-}
{-#LANGUAGE TypeFamilies #-}

module Snake
  ( -- * Constructions
    -- $about
    Game(..)
    -- ** Base Functor
  , GameF(..)
    -- ** Fixed Point
  , Game'(..)
    -- ** Free Monad
  , GameT(..)
    -- * Playing the Game
  , GameState
  , Snake
  , Direction(..)
  , play
  , play'
  , makeGetDirection
  , printState
    -- ** DSL
    -- $dsl
  , left
  , right
  , up
  , down
  , die
  , left'
  , right'
  , up'
  , down'
  , die'
    -- * Conversions
  , sequence'
  , sequenceT
  , toFix
  , fromFix
  , convert
  , convert'
  ) where

import Control.Applicative ((<$>), Applicative(..))
import Control.Comonad (Comonad(..))
import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar, tryTakeMVar, threadDelay)
import Control.Monad (join, void)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Free (FreeF(..), FreeT(..), free, runFree)
import Data.Biapplicative (Biapplicative(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Bifunctor.Flip (Flip(..))
import Data.Binary (Binary)
import Data.Data (Data)
import Data.Foldable (Foldable)
import Data.Functor.Classes (Read1(..), Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Foldable (Base, Fix(..), refix)
import qualified Data.Functor.Foldable as R (Foldable(..), Unfoldable(..))
import Data.Functor.Identity (Identity(..))
import Data.Set (fromList, member)
import Data.Maybe (maybe)
import Data.Traversable (Traversable(..))
import Data.Typeable (Typeable)
import Data.Void (Void, absurd)
import GHC.Generics (Generic)
import Prelude hiding (Left, Right, sequence)
import System.IO (BufferMode(..), hSetBuffering, hSetEcho, stdin)

{- Game -}

-- $about This module describes a snake game in terms of three constructions:
--
--   1. A recursive datatype, 'Game'
--   2. The fixed point of a base functor 'GameF'
--   3. The free monad over 'GameF'
--
-- We can convert to and from these constructions freely, and each
-- representation affords its own benefits and tradeoffs:
--
--   * 'Game' is readily serializable.
--   * 'Game'' and 'GameT' allow us to unfold the snake game in response to
--     effects (for example, user input).
--   * 'GameT' offers a DSL for constructing snake games.
--
-- Playing the snake game typically occurs in some monad @m@ (for example,
-- @IO@) as
--
--   * A value of type @'Game'' m 'GameState'@
--   * A value of type @'GameT' m 'GameState' Void@
--
-- See 'play' and 'play'' for examples.
--
-- The 'GameState' simply defines the current location and length of the snake
-- (see 'Snake') and the bounds of the play area.

data Game a
  = Left  a (Game a)  -- ^ The 'Snake' is moving 'L'eft.
  | Right a (Game a)  -- ^ The 'Snake' is moving 'R'ight.
  | Up    a (Game a)  -- ^ The 'Snake' is moving 'U'p.
  | Down  a (Game a)  -- ^ The 'Snake' is moving 'D'own.
  | Dead  a           -- ^ The 'Snake' collided with something and died.
  deriving (Data, Eq, Foldable, Functor, Generic, Ord, Read, Show, Traversable,
            Typeable)

instance Binary a => Binary (Game a)

instance Comonad Game where
  duplicate wa@(Left  a g) = Left  wa $ duplicate g
  duplicate wa@(Right a g) = Right wa $ duplicate g
  duplicate wa@(Up    a g) = Up    wa $ duplicate g
  duplicate wa@(Down  a g) = Down  wa $ duplicate g
  duplicate wa@(Dead  a)   = Dead  wa

  extract (Left  a _) = a
  extract (Right a _) = a
  extract (Up    a _) = a
  extract (Down  a _) = a
  extract (Dead  a)   = a

type instance Base (Game a) = Compose Identity (GameF a)

instance R.Foldable (Game a) where
  project (Left  a g) = Compose . Identity $ LeftF  a g
  project (Right a g) = Compose . Identity $ RightF a g
  project (Up    a g) = Compose . Identity $ UpF    a g
  project (Down  a g) = Compose . Identity $ DownF  a g
  project (Dead  a)   = Compose . Identity $ DeadF  a

instance R.Unfoldable (Game a) where
  embed (Compose (Identity (LeftF  a g))) = Left  a g
  embed (Compose (Identity (RightF a g))) = Right a g
  embed (Compose (Identity (UpF    a g))) = Up    a g
  embed (Compose (Identity (DownF  a g))) = Down  a g
  embed (Compose (Identity (DeadF  a)))   = Dead  a

-- | 'GameF' is the base functor of 'Game', which we can derive mechanically by
-- parameterizing all the recursive positions in 'Game'.
data GameF a b
  = LeftF  a b  -- ^ The 'Snake' is moving 'L'eft.
  | RightF a b  -- ^ The 'Snake' is moving 'R'ight.
  | UpF    a b  -- ^ The 'Snake' is moving 'U'p.
  | DownF  a b  -- ^ The 'Snake' is moving 'D'own.
  | DeadF  a    -- ^ The 'Snake' collided with something and died.
  deriving (Data, Eq, Foldable, Functor, Generic, Ord, Read, Show, Traversable,
            Typeable)

instance Applicative (Flip GameF b) where
  mf <*> ma = extract mf <$> ma
  pure = Flip . DeadF

instance Biapplicative GameF where
  bipure = RightF
  DeadF  f   <<*>> game = DeadF . f . extract $ Flip game
  LeftF  f g <<*>> game = bimap f g game
  RightF f g <<*>> game = bimap f g game
  UpF    f g <<*>> game = bimap f g game
  DownF  f g <<*>> game = bimap f g game

instance Bifunctor GameF where
  bimap ab cd (LeftF  a c) = LeftF  (ab a) $ cd c
  bimap ab cd (RightF a c) = RightF (ab a) $ cd c
  bimap ab cd (UpF    a c) = UpF    (ab a) $ cd c
  bimap ab cd (DownF  a c) = DownF  (ab a) $ cd c
  bimap ab _  (DeadF  a)   = DeadF $ ab a

instance Comonad (Flip GameF b) where
  duplicate wa@(Flip (LeftF  a b)) = Flip $ LeftF  wa b
  duplicate wa@(Flip (RightF a b)) = Flip $ RightF wa b
  duplicate wa@(Flip (UpF    a b)) = Flip $ UpF    wa b
  duplicate wa@(Flip (DownF  a b)) = Flip $ DownF  wa b
  duplicate wa@(Flip (DeadF  a))   = Flip $ DeadF  wa

  extract (Flip (LeftF  a _)) = a
  extract (Flip (RightF a _)) = a
  extract (Flip (UpF    a _)) = a
  extract (Flip (DownF  a _)) = a
  extract (Flip (DeadF  a))   = a

instance Monad (Flip GameF b) where
  ma >>= f = f $ extract ma
  return = pure

instance Read a => Read1 (GameF a) where
  readsPrec1 = readsPrec

instance Show a => Show1 (GameF a) where
  showsPrec1 = showsPrec

-- | 'Game'' is the fixed-point of the composition of a monad @m@ and 'GameF'.
-- By choosing @m@ you can choose the effects interleaved in the construction
-- of the game.
newtype Game' m a = Game' { getGame' :: Fix (Compose m (GameF a)) }
  deriving (Generic)

unFix :: Fix f -> f (Fix f)
unFix (Fix f) = f

deriving instance (Functor m, Show1 m, Show a) => Show (Game' m a)

instance Functor m => Functor (Game' m) where
  fmap f = Game' . Fix . Compose
         . fmap (bimap f (getGame' . fmap f . Game'))
         . getCompose . unFix . getGame'

type instance Base (Game' m a) = Compose m (GameF a)

instance Functor m => R.Foldable (Game' m a) where
  project = fmap Game' . unFix . getGame'

instance Functor m => R.Unfoldable (Game' m a) where
  embed = Game' . Fix . fmap getGame'

-- | 'GameT' is the free monad over the composition of a monad @m@ and 'GameF'.
-- By choosing @m@ you can choose the effects interleaved in the construction
-- of the game.
newtype GameT m a b = GameT { getGameT :: FreeT (GameF a) m b }
  deriving (Applicative, Foldable, Functor, Generic, Monad, Traversable)

-- | The 'Snake' is a list of the X/Y coordinates of its segments.
type Snake = [(Int, Int)]

-- | 'GameState' is a tuple of the X/Y bounds of the game space and the 'Snake'.
type GameState = ((Int, Int), Snake)

defaultBounds = (20, 20)
defaultSnake = [(4, 4), (3, 4), (2, 4), (1, 4)]
defaultGameState = (defaultBounds, defaultSnake)

defaultGame :: GameF GameState GameState
defaultGame = bipure defaultGameState defaultGameState

-- | 'Direction' is the direction the 'Snake' is moving in.
data Direction
  = L  -- ^ Left
  | R  -- ^ Right
  | U  -- ^ Up
  | D  -- ^ Down
  deriving (Bounded, Data, Enum, Eq, Generic, Ord, Read, Show, Typeable)

instance Binary Direction

{- Fixed Point & Free Monad Constructions -}

{- Conversions -}

-- | Convert from the fixed-point of the composition of a monad @m@ and a
-- functor @f@ to the free monad transformer over @m@ and @f@ by replacing all
-- occurrences of @Fix . Compose@ with @Free@.
fromFix :: (Functor f, Functor m) => Fix (Compose m f) -> (forall a. FreeT f m a)
fromFix = FreeT . fmap (Free . fmap fromFix) . getCompose . unFix

-- | Convert from the free monad transformer over a monad @m@ and a functor @f@
-- to the fixed-point of the composition of @m@ and @f@ by replacing all
-- occurences of @Free@ with @Fix . Compose@.
--
-- Note that this only works when
-- the constructor @Pure@ is never used, as witnessed by @Void@.
toFix :: (Functor f, Functor m) => FreeT f m Void -> Fix (Compose m f)
toFix = Fix . Compose . fmap go . runFreeT where
  go (Pure v) = absurd v
  go (Free freet) = fmap toFix freet where

sequenceFix
  :: (Functor f, Functor g)
  => (f (g (Fix f')) -> g (f' (Fix f')))  -- ^ A function to shuffle the layers
                                          -- around
  -> Fix f
  -> g (Fix f')
sequenceFix semisequence
  = fmap Fix . semisequence . fmap (sequenceFix semisequence) . unFix

-- | 'sequence'' is a version of @sequence@ that operates on the fixed-point of
-- the composition of an applicative @m@ and a traversable @f@; it sequences
-- the effects of @m@ and replaces it with @Identity@.
sequence'
  :: (Functor m, Monad m, Functor f, Traversable f)
  => Fix (Compose m f)
  -> m (Fix (Compose Identity f))
sequence' = sequenceFix semisequence where
  semisequence = fmap (Compose . Identity) . join . fmap sequence . getCompose

-- | 'sequenceT' is a version of @sequence@ that operates on the free monad
-- transformer over a monad @m@ and a traversable @f@; it sequences the effects
-- of @m@ and replaces it with @Identity@.
sequenceT
  :: (Functor m, Monad m, Functor f, Traversable f)
  => FreeT f m Void
  -> m (FreeT f Identity Void)
sequenceT = undefined

getFree :: FreeF f Void a -> f a
getFree (Free f) = f

convert :: (Functor m, Monad m) => Game' m a -> m (Game a)
convert = fmap refix . sequence' . getGame'

convert' :: (Functor m, Monad m) => GameT m a Void -> m (Game a)
convert' = convert . Game' . toFix . getGameT

{- Game Rules -}

-- | Compute the next step of the 'Game'.
step :: GameF GameState GameState -> GameF GameState GameState
step game@(DeadF _) = game
step game =
  let state@(bounds@(x, y), snake@(head:tail)) = extract $ Flip game
      newHead@(sX', sY') = nextHead game head
  in  if sX' < 0 || sY' < 0 ||  -- Check for collisions.
         sX' > x || sY' > y ||
         elem newHead tail
    then DeadF state
    else let state' = (bounds, take (length snake) (newHead:snake))
         in  bimap (const state') (const state') game
  where
    nextHead (LeftF  _ _) (sX, sY) = (sX-1, sY)
    nextHead (RightF _ _) (sX, sY) = (sX+1, sY)
    nextHead (UpF    _ _) (sX, sY) = (sX, sY-1)
    nextHead (DownF  _ _) (sX, sY) = (sX, sY+1)

-- | Change the 'Snake's 'Direction'.
changeDirection :: Direction -> GameF a b -> GameF a b
changeDirection newDir game
    | newDir == L && isRight game ||  -- Disallow 180° turns.
      newDir == R && isLeft  game ||
      newDir == U && isDown  game ||
      newDir == D && isUp    game
    = game
    | otherwise = bimap const const game <<*>> fromDirection newDir () ()
  where
    isLeft  (LeftF  _ _) = True
    isLeft  _            = False
    isRight (RightF _ _) = True
    isRight _            = False
    isUp    (UpF    _ _) = True
    isUp    _            = False
    isDown  (DownF  _ _) = True
    isDown  _            = False
    fromDirection L = LeftF
    fromDirection R = RightF
    fromDirection U = UpF
    fromDirection D = DownF

{- Playing the Game -}

printState :: MonadIO m => GameState -> m ()
printState ((x, y), snake) = do
  let points = fromList snake
  liftIO . putStrLn $ unlines
    [[if member (x, y) points then '#' else '.'
      | x <- [0..x]] | y <- [0..y]]

printState' :: MonadIO m => GameF GameState a -> m ()
printState' = printState . extract . Flip

{- Fixed Point -}

play
 :: (Functor m, Monad m)
  => m (Maybe Direction)
  -> (GameState -> m ())  -- ^ A \"print\" function to be run at the
                          -- start of every step
  -> m (Game' m GameState)
play getDirection printState = go getDirection defaultGame where
  go _ (DeadF state) = return . Game' . Fix . Compose . return $ DeadF state
  go getDirection game = do
    printState . extract $ Flip game
    dir <- getDirection
    let game' = maybe game (`changeDirection` game) dir
    let next = step game'
    fmap (Game' . Fix . Compose . return) . sequence
      $ fmap (const . fmap getGame' $ go getDirection next) game'

{- Monadically -}

-- $dsl The free monad over 'GameF' offers a DSL for constructing snake games.
-- For example, you can do the following
--
-- @
-- game :: Game ()
-- game = runIdentity . convert' $ do
--   left
--   right
--   up
--   down
--   die
-- @

play'
  :: (Functor m, Monad m)
  => m (Maybe Direction)
  -> (GameState -> m ())  -- ^ A \"print\" function to be run at the
                          -- start of every step
  -> m (GameT m GameState Void)
play' getDirection printState = go getDirection defaultGame where
  go _ (DeadF state) = return . GameT . FreeT . return . Free $ DeadF state
  go getDirection game = do
    printState . extract $ Flip game
    dir <- getDirection
    let game' = maybe game (`changeDirection` game) dir
    let next = step game'
    fmap (GameT . FreeT . return . Free) . sequence
      $ fmap (const . fmap getGameT $ go getDirection next) game'

left :: Monad m => GameT m () ()
left = left' ()

right :: Monad m => GameT m () ()
right = right' ()

up :: Monad m => GameT m () ()
up = up' ()

down :: Monad m => GameT m () ()
down = down' ()

die :: Monad m => GameT m () r
die = die' ()

left' :: Monad m => a -> GameT m a ()
left' a = GameT . FreeT . return . Free $ LeftF a (FreeT . return $ Pure ())

right' :: Monad m => a -> GameT m a ()
right' a = GameT . FreeT . return . Free $ RightF a (FreeT . return $ Pure ())

up' :: Monad m => a -> GameT m a ()
up' a = GameT . FreeT . return . Free $ UpF a (FreeT . return $ Pure ())

down' :: Monad m => a -> GameT m a ()
down' a = GameT . FreeT . return . Free $ DownF a (FreeT . return $ Pure ())

die' :: Monad m => a -> GameT m a r
die' a = GameT . FreeT . return . Free $ DeadF a

test :: Game ()
test = runIdentity . convert' $ do
  left
  right
  up
  down
  die

makeGetDirection :: IO (IO (Maybe Direction))
makeGetDirection = do
  hSetBuffering stdin NoBuffering
  hSetEcho stdin False
  -- Clock thread for sampling user input
  clock <- newEmptyMVar
  forkIO $
    let loop = do
        threadDelay 125000
        putMVar clock ()
        loop
    in  loop
  -- User input thread
  direction <- newEmptyMVar
  forkIO $
    let loop = do
        c <- getChar
        let d = case c of
              'a' -> Just L
              'd' -> Just R
              'w' -> Just U
              's' -> Just D
              _   -> Nothing
        tryTakeMVar direction
        putMVar direction d
        loop
    in  loop
  -- Function for getting the Direction, if any
  let getDirection = do
      takeMVar clock
      direction <- tryTakeMVar direction
      return $ join direction
  return getDirection

main :: IO ()
main = do
  getDirection <- makeGetDirection
  -- gameT <- play' getDirection
  -- game <- convert' gameT
  game' <- play getDirection printState
  game <- convert game'
  print $ void game
