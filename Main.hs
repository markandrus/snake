{-#LANGUAGE DeriveDataTypeable #-}
{-#LANGUAGE DeriveFunctor #-}
{-#LANGUAGE DeriveFoldable #-}
{-#LANGUAGE DeriveGeneric #-}
{-#LANGUAGE DeriveTraversable #-}
{-#LANGUAGE FlexibleInstances #-}
{-#LANGUAGE StandaloneDeriving #-}
{-#LANGUAGE TypeFamilies #-}

module Snake
  ( GameF(..)
  , Game(..)
  , GameT(..)
  , GameIO
  , Direction(..)
  , GameState
  , Snake
  , play
  ) where

import Control.Applicative ((<$>))
import Control.Comonad (Comonad(..))
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar, tryTakeMVar)
import Control.Monad (join, void)
import Control.Monad.Trans.Free (FreeF(..), FreeT(..), free, runFree)
import Control.Monad.IO.Class (MonadIO(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Bifunctor.Flip (Flip(..))
import Data.Binary (Binary)
import Data.Data (Data)
import Data.Functor.Classes (Show1(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Foldable (Base, Fix(..))
-- import qualified Data.Functor.Foldable as R (Foldable(..), Unfoldable(..))
import Data.Functor.Identity (Identity(..))
import Data.Foldable (Foldable)
import Data.Maybe (maybe)
import Data.Set (fromList, member)
import Data.Traversable as T (Traversable(..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Prelude hiding (sequence)
import System.IO (BufferMode(..), getChar, hSetBuffering, hSetEcho, stdin)

-- | 'Direction' is the direction the 'Snake' is moving in.
data Direction
  = L  -- ^ Left
  | R  -- ^ Right
  | U  -- ^ Up
  | D  -- ^ Down
  deriving (Bounded, Data, Eq, Generic, Ord, Read, Show, Typeable)

instance Binary Direction

-- | 'GameF' is the 'Base' functor of the 'Game'.
data GameF a b
  = MoveF Direction a b  -- ^ The 'Snake' is moving.
  | DeadF a              -- ^ The 'Snake' collided with something and died.
  deriving (Data, Eq, Foldable, Functor, Generic, Ord, Read, Show, Traversable, Typeable)

instance Show a => Show1 (GameF a) where
  showsPrec1 = showsPrec

instance Bifunctor GameF where
  bimap ab cd (MoveF dir a c) = MoveF dir (ab a) $ cd c
  bimap ab _ (DeadF a) = DeadF $ ab a

instance Comonad (Flip GameF b) where
  duplicate wa@(Flip (MoveF dir a b)) = Flip $ MoveF dir wa b
  duplicate wa@(Flip (DeadF a)) = Flip $ DeadF wa

  extract (Flip (MoveF _ a _)) = a
  extract (Flip (DeadF a)) = a

-- | The 'Snake' is a list of the X/Y coordinates of its segments.
type Snake = [(Int, Int)]

-- | 'GameState' is a tuple of the X/Y bounds of the game space and the 'Snake'.
type GameState = ((Int, Int), Snake)

defaultBounds = (20, 20)
defaultSnake = [(4, 4), (3, 4), (2, 4), (1, 4)]
defaultGameState = (defaultBounds, defaultSnake)
defaultGame = MoveF R defaultGameState defaultGameState

-- | Compute the next step of the 'Game'.
step :: GameF GameState GameState -> GameF GameState GameState
step (MoveF dir state@(bounds@(x, y), snake@(head:tail)) _) =
  let newHead@(sX', sY') = nextHead dir head
  in  if sX' < 0 || sY' < 0 ||  -- Check for collisions.
         sX' > x || sY' > y ||
         elem newHead tail
    then DeadF state
    else let state' = (bounds, take (length snake) (newHead:snake))
         in  MoveF dir state' state'
  where
    nextHead L (sX, sY) = (sX-1, sY)
    nextHead R (sX, sY) = (sX+1, sY)
    nextHead U (sX, sY) = (sX, sY-1)
    nextHead D (sX, sY) = (sX, sY+1)
step game = game

-- | Change the 'Snake's 'Direction'.
changeDirection :: Direction -> GameF a b -> GameF a b
changeDirection newDir game@(MoveF dir a b)
  | newDir == L && dir == R ||  -- Disallow 180° turns.
    newDir == R && dir == L ||
    newDir == U && dir == D ||
    newDir == D && dir == U
  = game
  | otherwise = MoveF newDir a b
changeDirection _ game = game
 
newtype GameT f a = GameT { getGameT :: Fix (Compose f (GameF a)) }
  deriving (Generic)

deriving instance (Functor f, Show1 f, Show a) => Show (GameT f a)

type GameIO = GameT IO

unFix :: Fix t -> t (Fix t)
unFix (Fix f) = f

instance Functor f => Functor (GameT f) where
  fmap f = GameT . Fix . Compose . fmap f' . getCompose . unFix . getGameT
    where
      f' (DeadF a) = DeadF $ f a
      f' (MoveF d a game) = MoveF d (f a) (getGameT . fmap f $ GameT game)

-- type instance Base (GameT f a) = Compose f (GameF a)
-- instance Functor f => R.Foldable (GameT f a) where
--   project = fmap GameT . unFix . getGameT
-- instance Functor f => R.Unfoldable (GameT f a) where
--   embed = GameT . Fix . fmap getGameT

newtype Game a = Game { getGame :: Fix (GameF a) }
  deriving (Generic, Read, Show, Typeable)

instance Functor Game where
  fmap f = Game . Fix . f' . unFix . getGame
    where
      f' (DeadF a) = DeadF $ f a
      f' (MoveF d a game) = MoveF d (f a) (getGame . fmap f $ Game game)

newtype GameMT m a = GameMT { getGameMT :: FreeT (GameF a) m a }
  deriving (Generic)

type GameM a = GameMT Identity a

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

play' :: (Functor f, MonadIO f) => f (Maybe Direction) -> f (GameT f GameState)
play' getDirection = go getDirection defaultGame where
  go _ (DeadF state) = return . GameT . Fix . Compose . return $ DeadF state
  go getDirection game = do
    printState . extract $ Flip game
    dir <- getDirection
    let game' = maybe game (`changeDirection` game) dir
    let next = step game'
    return . GameT . Fix . fmap getGameT . Compose . sequence
      $ fmap (go getDirection . const next) game'

  printState ((x, y), snake) = do
    let points = fromList snake
    liftIO . putStrLn $ unlines
      [[if member (x, y) points then '#' else '.'
        | x <- [0..x]] | y <- [0..y]]

play :: IO (GameT IO GameState)
play = makeGetDirection >>= play'

evaluate :: (Functor f, Monad f) => GameT f a -> f (GameT Identity a)
evaluate (GameT (Fix (Compose ma)))
    = GameT . Fix . Compose . Identity <$> (ma >>= go)
  where
    go (DeadF a) = return $ DeadF a
    go (MoveF dir a (Fix (Compose ma)))
      = (MoveF dir a . Fix . Compose . Identity) <$> (ma >>= go)

-- Thanks to /r/brianhamrick:
-- http://www.reddit.com/r/haskell/comments/2rzwmp/fix_compose_io_f_io_fix_compose_identity_f/cnkvdif
sequenceFix
  :: (Functor f, Functor g)
  => (f (g (Fix f')) -> g (f' (Fix f')))
  -> Fix f
  -> g (Fix f')
sequenceFix semisequence
  = fmap Fix . semisequence . fmap (sequenceFix semisequence) . unFix

evaluate' :: (Functor f, Monad f) => GameT f a -> f (Game a)
evaluate' (GameT game) = Game <$> go game where
  -- go :: Fix (Compose IO (GameF a)) -> IO (Fix (GameF a))
  go = sequenceFix semisequence where
    -- semisequence :: Compose IO (GameF a) (IO (Fix (GameF a)))
    --              -> IO (GameF a (Fix (GameF a)))
    semisequence = (sequence =<<) . getCompose

main :: IO ()
main = play >>= evaluate' >>= (print . void)
